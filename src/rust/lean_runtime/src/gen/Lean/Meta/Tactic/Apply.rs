// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Lean.Meta.Tactic.Util Lean.PrettyPrinter Lean.Meta.AppBuilder Init.Omega
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_List_get___redArg,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_beta, l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MessageData_ofLazyM,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaBoundedTelescope, l_Lean_Meta_forallMetaTelescopeReducing,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_isExprDefEqGuarded,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::Check::{
    l_Lean_Meta_addPPExplicitToExposeDiff, l_Lean_Meta_mkUnfoldAxiomsNote,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVarsNoDelayed;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_MVarId_getType, l_Lean_MVarId_getType_x27, l_Lean_MVarId_headBetaType,
    l_Lean_MVarId_setTag___redArg, l_Lean_Meta_appendTag,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___redArg,
    runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, runtime_initialize_Lean_PrettyPrinter,
};
use crate::r#gen::Lean::Util::FindMVar::l_Lean_FindMVar_main;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_5, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_getExpectedNumArgsAux___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_getExpectedNumArgsAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getExpectedNumArgsAux___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_getExpectedNumArgsAux___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_getExpectedNumArgsAux___closed__1: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [10, 119, 105, 116, 104, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 117, 110, 105, 102, 121, 32, 116, 104, 101, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 104, 101, 32, 116, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value) as *mut LeanObject,110479913597202347 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [84, 104, 101, 32, 102, 117, 108, 108, 32, 116, 121, 112, 101, 32, 111, 102, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 115, 115, 105, 103, 110, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value
) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value
) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyConst___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_Lean_MVarId_applyConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyConst___closed__0_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyConst___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyConst___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            84, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 58, 32, 116, 97, 114, 103,
            101, 116, 32, 105, 115, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyN___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__2_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            10, 98, 117, 116, 32, 97, 112, 112, 108, 105, 101, 100, 32, 101, 120, 112, 114, 101,
            115, 115, 105, 111, 110, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyN___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__4_value: LeanStringObject<17> =
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
            10, 97, 102, 116, 101, 114, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyN___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__6_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 46, 0],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__6_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyN___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__8_value: LeanStringObject<31> =
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
            65, 112, 112, 108, 105, 101, 100, 32, 116, 121, 112, 101, 32, 116, 97, 107, 101, 115,
            32, 102, 101, 119, 101, 114, 32, 116, 104, 97, 110, 32, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__8_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyN___lam__0___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__10_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 58, 10, 0],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__10_value) as *mut LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_applyN___lam__0___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 110, 100, 0],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value
        ) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value
        ) as *mut LeanObject,
        8738205681931236784 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value
) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value
        ) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value) as *mut LeanObject,11695081953491693114 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_splitAndCore___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 112, 108, 105, 116, 65, 110, 100, 0],
};
static mut l_Lean_MVarId_splitAndCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_splitAndCore___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_splitAndCore___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_splitAndCore___closed__0_value) as *mut LeanObject,
        2306458822834130193 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_splitAndCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_splitAndCore___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_exfalso___lam__0___closed__0_value: LeanStringObject<6> =
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
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_exfalso___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__0_value) as *mut LeanObject,
        907667957179513571 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_exfalso___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_exfalso___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_exfalso___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_exfalso___lam__0___closed__3_value: LeanStringObject<5> =
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
        m_data: [101, 108, 105, 109, 0],
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__3_value) as *mut LeanObject;
static l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__0_value) as *mut LeanObject,
        907667957179513571 as *mut LeanObject,
    ],
};
pub static l_Lean_MVarId_exfalso___lam__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__3_value) as *mut LeanObject,
        3404330064793727539 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_exfalso___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_MVarId_exfalso___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 120, 102, 97, 108, 115, 111, 0],
};
static mut l_Lean_MVarId_exfalso___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_exfalso___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_exfalso___closed__0_value) as *mut LeanObject,
        10107530215740819414 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_exfalso___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__0_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105,
            110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__4_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 100, 101, 120, 32, 0],
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__5_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 44, 32, 111, 110,
            108, 121, 32, 0,
        ],
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__6_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 0,
        ],
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__7_value: LeanStringObject<48> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            32, 116, 97, 99, 116, 105, 99, 32, 119, 111, 114, 107, 115, 32, 102, 111, 114, 32, 105,
            110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115, 32, 119, 105, 116,
            104, 32, 101, 120, 97, 99, 116, 108, 121, 32, 0,
        ],
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_MVarId_iffOfEq___lam__0___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 97, 105, 108, 101, 100, 0],
    };
static mut l_Lean_MVarId_iffOfEq___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_MVarId_iffOfEq___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_iffOfEq___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_iffOfEq___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 102, 102, 95, 111, 102, 95, 101, 113, 0],
};
static mut l_Lean_MVarId_iffOfEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_iffOfEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__0_value) as *mut LeanObject,
        18095603761325883834 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_iffOfEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_iffOfEq___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_iffOfEq___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_iffOfEq___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777472 as *mut LeanObject],
};
static mut l_Lean_MVarId_iffOfEq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__3_value) as *mut LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_MVarId_propext___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__0_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_propext___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__2_value: LeanStringObject<8> =
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
        m_data: [112, 114, 111, 112, 101, 120, 116, 0],
    };
static mut l_Lean_MVarId_propext___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__2_value) as *mut LeanObject,
        12404887534527682101 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_propext___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_MVarId_propext___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_propext___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0: u64 = 0;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value: LeanStringObject<4> =
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
        m_data: [72, 69, 113, 0],
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value)
                as *mut LeanObject,
            13589827700912665667 as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value: LeanStringObject<16> =
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
            112, 114, 111, 111, 102, 95, 105, 114, 114, 101, 108, 95, 104, 101, 113, 0,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value)
                as *mut LeanObject,
            16338550082024008116 as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        112, 114, 111, 111, 102, 73, 114, 114, 101, 108, 72, 101, 113, 0,
    ],
};
static mut l_Lean_MVarId_proofIrrelHeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___closed__0_value) as *mut LeanObject,
        8208296555560902447 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_proofIrrelHeq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 0],
    };
static mut l_Lean_MVarId_subsingletonElim___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value)
        as *mut LeanObject;
static l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value)
                as *mut LeanObject,
            13409365605382521367 as *mut LeanObject,
        ],
    };
pub static l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__3_value)
                as *mut LeanObject,
            15293707491349124431 as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_subsingletonElim___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_MVarId_subsingletonElim___closed__0_value: LeanStringObject<17> =
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
            115, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 69, 108, 105, 109, 0,
        ],
    };
static mut l_Lean_MVarId_subsingletonElim___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_subsingletonElim___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___closed__0_value) as *mut LeanObject,
        16518798283969257801 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_subsingletonElim___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(
    mut v_k_3654_: *mut LeanObject,
    mut v_b_3655_: *mut LeanObject,
    mut v_c_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3660_);
    lean_inc_ref(v___y_3659_);
    lean_inc(v___y_3658_);
    lean_inc_ref(v___y_3657_);
    v___x_3662_ = lean_apply_7(
        v_k_3654_,
        v_b_3655_,
        v_c_3656_,
        v___y_3657_,
        v___y_3658_,
        v___y_3659_,
        v___y_3660_,
        lean_box(0),
    );
    return v___x_3662_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(
    mut v_k_3663_: *mut LeanObject,
    mut v_b_3664_: *mut LeanObject,
    mut v_c_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3671_: *mut LeanObject = core::ptr::null_mut();
    v_res_3671_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_3663_, v_b_3664_, v_c_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
    lean_dec(v___y_3669_);
    lean_dec_ref(v___y_3668_);
    lean_dec(v___y_3667_);
    lean_dec_ref(v___y_3666_);
    return v_res_3671_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(
    mut v_type_3672_: *mut LeanObject,
    mut v_k_3673_: *mut LeanObject,
    mut v_cleanupAnnotations_3674_: u8,
    mut v_whnfType_3675_: u8,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_a_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3681_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_3681_, 0, v_k_3673_);
                v___x_3682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_3672_,
                    v___f_3681_,
                    v_cleanupAnnotations_3674_,
                    v_whnfType_3675_,
                    v___y_3676_,
                    v___y_3677_,
                    v___y_3678_,
                    v___y_3679_,
                );
                if lean_obj_tag(v___x_3682_) == 0 {
                    v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
                    v_isSharedCheck_3690_ = (!lean_is_exclusive(v___x_3682_)) as u8;
                    if v_isSharedCheck_3690_ == 0 {
                        v___x_3685_ = v___x_3682_;
                        v_isShared_3686_ = v_isSharedCheck_3690_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3683_);
                        lean_dec(v___x_3682_);
                        v___x_3685_ = lean_box(0);
                        v_isShared_3686_ = v_isSharedCheck_3690_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3691_ = lean_ctor_get(v___x_3682_, 0);
                    v_isSharedCheck_3698_ = (!lean_is_exclusive(v___x_3682_)) as u8;
                    if v_isSharedCheck_3698_ == 0 {
                        v___x_3693_ = v___x_3682_;
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3691_);
                        lean_dec(v___x_3682_);
                        v___x_3693_ = lean_box(0);
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3686_ == 0 {
                    v___x_3688_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
                    v___x_3688_ = v_reuseFailAlloc_3689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3688_;
            }
            3 => {
                if v_isShared_3694_ == 0 {
                    v___x_3696_ = v___x_3693_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
                    v___x_3696_ = v_reuseFailAlloc_3697_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(
    mut v_type_3699_: *mut LeanObject,
    mut v_k_3700_: *mut LeanObject,
    mut v_cleanupAnnotations_3701_: *mut LeanObject,
    mut v_whnfType_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3708_: u8 = 0;
    let mut v_whnfType_boxed_3709_: u8 = 0;
    let mut v_res_3710_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3708_ = (lean_unbox(v_cleanupAnnotations_3701_) as u8);
    v_whnfType_boxed_3709_ = (lean_unbox(v_whnfType_3702_) as u8);
    v_res_3710_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_3699_, v_k_3700_, v_cleanupAnnotations_boxed_3708_, v_whnfType_boxed_3709_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
    lean_dec(v___y_3706_);
    lean_dec_ref(v___y_3705_);
    lean_dec(v___y_3704_);
    lean_dec_ref(v___y_3703_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(
    mut v_00_u03b1_3711_: *mut LeanObject,
    mut v_type_3712_: *mut LeanObject,
    mut v_k_3713_: *mut LeanObject,
    mut v_cleanupAnnotations_3714_: u8,
    mut v_whnfType_3715_: u8,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
    mut v___y_3718_: *mut LeanObject,
    mut v___y_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    v___x_3721_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_3712_, v_k_3713_, v_cleanupAnnotations_3714_, v_whnfType_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
    return v___x_3721_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(
    mut v_00_u03b1_3722_: *mut LeanObject,
    mut v_type_3723_: *mut LeanObject,
    mut v_k_3724_: *mut LeanObject,
    mut v_cleanupAnnotations_3725_: *mut LeanObject,
    mut v_whnfType_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
    mut v___y_3729_: *mut LeanObject,
    mut v___y_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3732_: u8 = 0;
    let mut v_whnfType_boxed_3733_: u8 = 0;
    let mut v_res_3734_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3732_ = (lean_unbox(v_cleanupAnnotations_3725_) as u8);
    v_whnfType_boxed_3733_ = (lean_unbox(v_whnfType_3726_) as u8);
    v_res_3734_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(
            v_00_u03b1_3722_,
            v_type_3723_,
            v_k_3724_,
            v_cleanupAnnotations_boxed_3732_,
            v_whnfType_boxed_3733_,
            v___y_3727_,
            v___y_3728_,
            v___y_3729_,
            v___y_3730_,
        );
    lean_dec(v___y_3730_);
    lean_dec_ref(v___y_3729_);
    lean_dec(v___y_3728_);
    lean_dec_ref(v___y_3727_);
    return v_res_3734_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux___lam__0(
    mut v_xs_3735_: *mut LeanObject,
    mut v_body_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    v___x_3742_ = lean_array_get_size(v_xs_3735_);
    v___x_3743_ = l_Lean_Expr_getAppFn(v_body_3736_);
    v___x_3744_ = l_Lean_Expr_isMVar(v___x_3743_);
    lean_dec_ref(v___x_3743_);
    v___x_3745_ = lean_box((v___x_3744_) as usize);
    v___x_3746_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3746_, 0, v___x_3742_);
    lean_ctor_set(v___x_3746_, 1, v___x_3745_);
    v___x_3747_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3747_, 0, v___x_3746_);
    return v___x_3747_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(
    mut v_xs_3748_: *mut LeanObject,
    mut v_body_3749_: *mut LeanObject,
    mut v___y_3750_: *mut LeanObject,
    mut v___y_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3755_: *mut LeanObject = core::ptr::null_mut();
    v_res_3755_ = l_Lean_Meta_getExpectedNumArgsAux___lam__0(
        v_xs_3748_,
        v_body_3749_,
        v___y_3750_,
        v___y_3751_,
        v___y_3752_,
        v___y_3753_,
    );
    lean_dec(v___y_3753_);
    lean_dec_ref(v___y_3752_);
    lean_dec(v___y_3751_);
    lean_dec_ref(v___y_3750_);
    lean_dec_ref(v_body_3749_);
    lean_dec_ref(v_xs_3748_);
    return v_res_3755_;
}
pub unsafe fn _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1() -> u64 {
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: u64 = 0;
    v___x_3757_ = 1;
    v___x_3758_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux(
    mut v_e_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
    mut v_a_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
    mut v_a_3763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3766_: u8 = 0;
    let mut v_ctxApprox_3767_: u8 = 0;
    let mut v_quasiPatternApprox_3768_: u8 = 0;
    let mut v_constApprox_3769_: u8 = 0;
    let mut v_isDefEqStuckEx_3770_: u8 = 0;
    let mut v_unificationHints_3771_: u8 = 0;
    let mut v_proofIrrelevance_3772_: u8 = 0;
    let mut v_assignSyntheticOpaque_3773_: u8 = 0;
    let mut v_offsetCnstrs_3774_: u8 = 0;
    let mut v_etaStruct_3775_: u8 = 0;
    let mut v_univApprox_3776_: u8 = 0;
    let mut v_iota_3777_: u8 = 0;
    let mut v_beta_3778_: u8 = 0;
    let mut v_proj_3779_: u8 = 0;
    let mut v_zeta_3780_: u8 = 0;
    let mut v_zetaDelta_3781_: u8 = 0;
    let mut v_zetaUnused_3782_: u8 = 0;
    let mut v_zetaHave_3783_: u8 = 0;
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v_trackZetaDelta_3787_: u8 = 0;
    let mut v_zetaDeltaSet_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3794_: u8 = 0;
    let mut v_inTypeClassResolution_3795_: u8 = 0;
    let mut v_cacheInferType_3796_: u8 = 0;
    let mut v___x_3797_: u8 = 0;
    let mut v_config_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u64 = 0;
    let mut v___x_3801_: u64 = 0;
    let mut v___x_3802_: u64 = 0;
    let mut v___f_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: u64 = 0;
    let mut v___x_3806_: u64 = 0;
    let mut v_key_3807_: u64 = 0;
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3765_ = l_Lean_Meta_Context_config(v_a_3760_);
                v_foApprox_3766_ = lean_ctor_get_uint8(v___x_3765_, 0 as u32);
                v_ctxApprox_3767_ = lean_ctor_get_uint8(v___x_3765_, 1 as u32);
                v_quasiPatternApprox_3768_ = lean_ctor_get_uint8(v___x_3765_, 2 as u32);
                v_constApprox_3769_ = lean_ctor_get_uint8(v___x_3765_, 3 as u32);
                v_isDefEqStuckEx_3770_ = lean_ctor_get_uint8(v___x_3765_, 4 as u32);
                v_unificationHints_3771_ = lean_ctor_get_uint8(v___x_3765_, 5 as u32);
                v_proofIrrelevance_3772_ = lean_ctor_get_uint8(v___x_3765_, 6 as u32);
                v_assignSyntheticOpaque_3773_ = lean_ctor_get_uint8(v___x_3765_, 7 as u32);
                v_offsetCnstrs_3774_ = lean_ctor_get_uint8(v___x_3765_, 8 as u32);
                v_etaStruct_3775_ = lean_ctor_get_uint8(v___x_3765_, 10 as u32);
                v_univApprox_3776_ = lean_ctor_get_uint8(v___x_3765_, 11 as u32);
                v_iota_3777_ = lean_ctor_get_uint8(v___x_3765_, 12 as u32);
                v_beta_3778_ = lean_ctor_get_uint8(v___x_3765_, 13 as u32);
                v_proj_3779_ = lean_ctor_get_uint8(v___x_3765_, 14 as u32);
                v_zeta_3780_ = lean_ctor_get_uint8(v___x_3765_, 15 as u32);
                v_zetaDelta_3781_ = lean_ctor_get_uint8(v___x_3765_, 16 as u32);
                v_zetaUnused_3782_ = lean_ctor_get_uint8(v___x_3765_, 17 as u32);
                v_zetaHave_3783_ = lean_ctor_get_uint8(v___x_3765_, 18 as u32);
                v_isSharedCheck_3812_ = (!lean_is_exclusive(v___x_3765_)) as u8;
                if v_isSharedCheck_3812_ == 0 {
                    v___x_3785_ = v___x_3765_;
                    v_isShared_3786_ = v_isSharedCheck_3812_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_3765_);
                    v___x_3785_ = lean_box(0);
                    v_isShared_3786_ = v_isSharedCheck_3812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3787_ = lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3788_ = lean_ctor_get(v_a_3760_, 1);
                v_lctx_3789_ = lean_ctor_get(v_a_3760_, 2);
                v_localInstances_3790_ = lean_ctor_get(v_a_3760_, 3);
                v_defEqCtx_x3f_3791_ = lean_ctor_get(v_a_3760_, 4);
                v_synthPendingDepth_3792_ = lean_ctor_get(v_a_3760_, 5);
                v_canUnfold_x3f_3793_ = lean_ctor_get(v_a_3760_, 6);
                v_univApprox_3794_ = lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3795_ = lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3796_ = lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_3797_ = 1;
                if v_isShared_3786_ == 0 {
                    v_config_3799_ = v___x_3785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 0 as u32, v_foApprox_3766_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 1 as u32, v_ctxApprox_3767_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        2 as u32,
                        v_quasiPatternApprox_3768_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 3 as u32, v_constApprox_3769_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 4 as u32, v_isDefEqStuckEx_3770_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 5 as u32, v_unificationHints_3771_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 6 as u32, v_proofIrrelevance_3772_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        7 as u32,
                        v_assignSyntheticOpaque_3773_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 8 as u32, v_offsetCnstrs_3774_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 10 as u32, v_etaStruct_3775_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 11 as u32, v_univApprox_3776_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 12 as u32, v_iota_3777_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 13 as u32, v_beta_3778_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 14 as u32, v_proj_3779_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 15 as u32, v_zeta_3780_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 16 as u32, v_zetaDelta_3781_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 17 as u32, v_zetaUnused_3782_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3811_, 18 as u32, v_zetaHave_3783_);
                    v_config_3799_ = v_reuseFailAlloc_3811_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_3799_, 9 as u32, v___x_3797_);
                v___x_3800_ = l_Lean_Meta_Context_configKey(v_a_3760_);
                v___x_3801_ = 3u64;
                v___x_3802_ = lean_uint64_shift_right(v___x_3800_, v___x_3801_);
                v___f_3803_ = l_Lean_Meta_getExpectedNumArgsAux___closed__0;
                v___x_3804_ = 0;
                v___x_3805_ = lean_uint64_shift_left(v___x_3802_, v___x_3801_);
                v___x_3806_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getExpectedNumArgsAux___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getExpectedNumArgsAux___closed__1_once),
                    _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1,
                );
                v_key_3807_ = lean_uint64_lor(v___x_3805_, v___x_3806_);
                v___x_3808_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_3808_, 0, v_config_3799_);
                lean_ctor_set_uint64(
                    v___x_3808_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_3807_,
                );
                lean_inc(v_canUnfold_x3f_3793_);
                lean_inc(v_synthPendingDepth_3792_);
                lean_inc(v_defEqCtx_x3f_3791_);
                lean_inc_ref(v_localInstances_3790_);
                lean_inc_ref(v_lctx_3789_);
                lean_inc(v_zetaDeltaSet_3788_);
                v___x_3809_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_3809_, 0, v___x_3808_);
                lean_ctor_set(v___x_3809_, 1, v_zetaDeltaSet_3788_);
                lean_ctor_set(v___x_3809_, 2, v_lctx_3789_);
                lean_ctor_set(v___x_3809_, 3, v_localInstances_3790_);
                lean_ctor_set(v___x_3809_, 4, v_defEqCtx_x3f_3791_);
                lean_ctor_set(v___x_3809_, 5, v_synthPendingDepth_3792_);
                lean_ctor_set(v___x_3809_, 6, v_canUnfold_x3f_3793_);
                lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3787_,
                );
                lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3794_,
                );
                lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3795_,
                );
                lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3796_,
                );
                v___x_3810_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_3759_, v___f_3803_, v___x_3804_, v___x_3804_, v___x_3809_, v_a_3761_, v_a_3762_, v_a_3763_);
                lean_dec_ref_known(v___x_3809_, 7);
                return v___x_3810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux___boxed(
    mut v_e_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3819_: *mut LeanObject = core::ptr::null_mut();
    v_res_3819_ =
        l_Lean_Meta_getExpectedNumArgsAux(v_e_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
    lean_dec(v_a_3817_);
    lean_dec_ref(v_a_3816_);
    lean_dec(v_a_3815_);
    lean_dec_ref(v_a_3814_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgs(
    mut v_e_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_fst_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_a_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3826_ = l_Lean_Meta_getExpectedNumArgsAux(
                    v_e_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_,
                );
                if lean_obj_tag(v___x_3826_) == 0 {
                    v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
                    v_isSharedCheck_3835_ = (!lean_is_exclusive(v___x_3826_)) as u8;
                    if v_isSharedCheck_3835_ == 0 {
                        v___x_3829_ = v___x_3826_;
                        v_isShared_3830_ = v_isSharedCheck_3835_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3827_);
                        lean_dec(v___x_3826_);
                        v___x_3829_ = lean_box(0);
                        v_isShared_3830_ = v_isSharedCheck_3835_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3836_ = lean_ctor_get(v___x_3826_, 0);
                    v_isSharedCheck_3843_ = (!lean_is_exclusive(v___x_3826_)) as u8;
                    if v_isSharedCheck_3843_ == 0 {
                        v___x_3838_ = v___x_3826_;
                        v_isShared_3839_ = v_isSharedCheck_3843_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3836_);
                        lean_dec(v___x_3826_);
                        v___x_3838_ = lean_box(0);
                        v_isShared_3839_ = v_isSharedCheck_3843_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3831_ = lean_ctor_get(v_a_3827_, 0);
                lean_inc(v_fst_3831_);
                lean_dec(v_a_3827_);
                if v_isShared_3830_ == 0 {
                    lean_ctor_set(v___x_3829_, 0, v_fst_3831_);
                    v___x_3833_ = v___x_3829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_fst_3831_);
                    v___x_3833_ = v_reuseFailAlloc_3834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3833_;
            }
            3 => {
                if v_isShared_3839_ == 0 {
                    v___x_3841_ = v___x_3838_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgs___boxed(
    mut v_e_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
    mut v_a_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3850_: *mut LeanObject = core::ptr::null_mut();
    v_res_3850_ =
        l_Lean_Meta_getExpectedNumArgs(v_e_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
    lean_dec(v_a_3848_);
    lean_dec_ref(v_a_3847_);
    lean_dec(v_a_3846_);
    lean_dec_ref(v_a_3845_);
    return v_res_3850_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0;
    v___x_3853_ = l_Lean_stringToMessageData(v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    v___x_3855_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2;
    v___x_3856_ = l_Lean_stringToMessageData(v___x_3855_);
    return v___x_3856_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3858_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4;
    v___x_3859_ = l_Lean_stringToMessageData(v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8()
-> *mut LeanObject {
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7;
    v___x_3864_ = l_Lean_MessageData_ofFormat(v___x_3863_);
    return v___x_3864_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(
    mut v___y_3867_: *mut LeanObject,
    mut v_targetType_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v_term_x3f_3870_: *mut LeanObject,
    mut v_conclusionType_x3f_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
    mut v___y_3875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3881_: u8 = 0;
    let mut v_fst_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___y_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_a_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3877_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                    v___y_3867_,
                    v_targetType_3868_,
                    v___y_3872_,
                    v___y_3873_,
                    v___y_3874_,
                    v___y_3875_,
                );
                if lean_obj_tag(v___x_3877_) == 0 {
                    v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
                    v_isSharedCheck_3919_ = (!lean_is_exclusive(v___x_3877_)) as u8;
                    if v_isSharedCheck_3919_ == 0 {
                        v___x_3880_ = v___x_3877_;
                        v_isShared_3881_ = v_isSharedCheck_3919_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3878_);
                        lean_dec(v___x_3877_);
                        v___x_3880_ = lean_box(0);
                        v_isShared_3881_ = v_isSharedCheck_3919_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_term_x3f_3870_);
                    lean_dec_ref(v___y_3869_);
                    v_a_3920_ = lean_ctor_get(v___x_3877_, 0);
                    v_isSharedCheck_3927_ = (!lean_is_exclusive(v___x_3877_)) as u8;
                    if v_isSharedCheck_3927_ == 0 {
                        v___x_3922_ = v___x_3877_;
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3920_);
                        lean_dec(v___x_3877_);
                        v___x_3922_ = lean_box(0);
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3882_ = lean_ctor_get(v_a_3878_, 0);
                v_snd_3883_ = lean_ctor_get(v_a_3878_, 1);
                v_isSharedCheck_3918_ = (!lean_is_exclusive(v_a_3878_)) as u8;
                if v_isSharedCheck_3918_ == 0 {
                    v___x_3885_ = v_a_3878_;
                    v_isShared_3886_ = v_isSharedCheck_3918_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3883_);
                    lean_inc(v_fst_3882_);
                    lean_dec(v_a_3878_);
                    v___x_3885_ = lean_box(0);
                    v_isShared_3886_ = v_isSharedCheck_3918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_conclusionType_x3f_3871_) == 0 {
                    v___x_3916_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9;
                    v___y_3906_ = v___x_3916_;
                    state = 6;
                    continue;
                } else {
                    v___x_3917_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10;
                    v___y_3906_ = v___x_3917_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_3886_ == 0 {
                    lean_ctor_set_tag(v___x_3885_, 7);
                    lean_ctor_set(v___x_3885_, 1, v___y_3890_);
                    lean_ctor_set(v___x_3885_, 0, v___y_3889_);
                    v___x_3892_ = v___x_3885_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___y_3889_);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___y_3890_);
                    v___x_3892_ = v_reuseFailAlloc_3904_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3893_ = l_Lean_indentExpr(v_fst_3882_);
                v___x_3894_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3894_, 0, v___x_3892_);
                lean_ctor_set(v___x_3894_, 1, v___x_3893_);
                v___x_3895_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
                v___x_3896_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3896_, 0, v___x_3894_);
                lean_ctor_set(v___x_3896_, 1, v___x_3895_);
                v___x_3897_ = l_Lean_indentExpr(v_snd_3883_);
                v___x_3898_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v___x_3896_);
                lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                v___x_3899_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3899_, 0, v___x_3898_);
                lean_ctor_set(v___x_3899_, 1, v___y_3869_);
                v___x_3900_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                lean_ctor_set(v___x_3900_, 1, v___y_3888_);
                if v_isShared_3881_ == 0 {
                    lean_ctor_set(v___x_3880_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3902_;
            }
            6 => {
                lean_inc(v_snd_3883_);
                lean_inc(v_fst_3882_);
                v___x_3907_ = l_Lean_Meta_mkUnfoldAxiomsNote(
                    v_fst_3882_,
                    v_snd_3883_,
                    v___y_3872_,
                    v___y_3873_,
                    v___y_3874_,
                    v___y_3875_,
                );
                if lean_obj_tag(v___x_3907_) == 0 {
                    v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
                    lean_inc(v_a_3908_);
                    lean_dec_ref_known(v___x_3907_, 1);
                    v___x_3909_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
                    lean_inc_ref(v___y_3906_);
                    v___x_3910_ = l_Lean_stringToMessageData(v___y_3906_);
                    v___x_3911_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3911_, 0, v___x_3909_);
                    lean_ctor_set(v___x_3911_, 1, v___x_3910_);
                    v___x_3912_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
                    v___x_3913_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3913_, 0, v___x_3911_);
                    lean_ctor_set(v___x_3913_, 1, v___x_3912_);
                    if lean_obj_tag(v_term_x3f_3870_) == 0 {
                        v___x_3914_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
                        v___y_3888_ = v_a_3908_;
                        v___y_3889_ = v___x_3913_;
                        v___y_3890_ = v___x_3914_;
                        state = 3;
                        continue;
                    } else {
                        v_val_3915_ = lean_ctor_get(v_term_x3f_3870_, 0);
                        lean_inc(v_val_3915_);
                        lean_dec_ref_known(v_term_x3f_3870_, 1);
                        v___y_3888_ = v_a_3908_;
                        v___y_3889_ = v___x_3913_;
                        v___y_3890_ = v_val_3915_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3885_);
                    lean_dec(v_snd_3883_);
                    lean_dec(v_fst_3882_);
                    lean_del_object(v___x_3880_);
                    lean_dec(v_term_x3f_3870_);
                    lean_dec_ref(v___y_3869_);
                    return v___x_3907_;
                }
            }
            7 => {
                if v_isShared_3923_ == 0 {
                    v___x_3925_ = v___x_3922_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(
    mut v___y_3928_: *mut LeanObject,
    mut v_targetType_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v_term_x3f_3931_: *mut LeanObject,
    mut v_conclusionType_x3f_3932_: *mut LeanObject,
    mut v___y_3933_: *mut LeanObject,
    mut v___y_3934_: *mut LeanObject,
    mut v___y_3935_: *mut LeanObject,
    mut v___y_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3938_: *mut LeanObject = core::ptr::null_mut();
    v_res_3938_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(
        v___y_3928_,
        v_targetType_3929_,
        v___y_3930_,
        v_term_x3f_3931_,
        v_conclusionType_x3f_3932_,
        v___y_3933_,
        v___y_3934_,
        v___y_3935_,
        v___y_3936_,
    );
    lean_dec(v___y_3936_);
    lean_dec_ref(v___y_3935_);
    lean_dec(v___y_3934_);
    lean_dec_ref(v___y_3933_);
    lean_dec(v_conclusionType_x3f_3932_);
    return v_res_3938_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    v___x_3943_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2;
    v___x_3944_ = l_Lean_stringToMessageData(v___x_3943_);
    return v___x_3944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    v___x_3946_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4;
    v___x_3947_ = l_Lean_stringToMessageData(v___x_3946_);
    return v___x_3947_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    v___x_3949_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6;
    v___x_3950_ = l_Lean_stringToMessageData(v___x_3949_);
    return v___x_3950_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(
    mut v_mvarId_3951_: *mut LeanObject,
    mut v_eType_3952_: *mut LeanObject,
    mut v_conclusionType_x3f_3953_: *mut LeanObject,
    mut v_targetType_3954_: *mut LeanObject,
    mut v_term_x3f_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
    mut v_a_3957_: *mut LeanObject,
    mut v_a_3958_: *mut LeanObject,
    mut v_a_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3961_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
                if lean_obj_tag(v_conclusionType_x3f_3953_) == 0 {
                    lean_inc_ref(v_eType_3952_);
                    v___y_3984_ = v_eType_3952_;
                    state = 3;
                    continue;
                } else {
                    v_val_3989_ = lean_ctor_get(v_conclusionType_x3f_3953_, 0);
                    lean_inc(v_val_3989_);
                    v___y_3984_ = v_val_3989_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_targetType_3954_);
                v___f_3965_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_3965_, 0, v___y_3963_);
                lean_closure_set(v___f_3965_, 1, v_targetType_3954_);
                lean_closure_set(v___f_3965_, 2, v___y_3964_);
                lean_closure_set(v___f_3965_, 3, v_term_x3f_3955_);
                lean_closure_set(v___f_3965_, 4, v_conclusionType_x3f_3953_);
                v___x_3966_ = lean_unsigned_to_nat(2);
                v___x_3967_ = lean_mk_empty_array_with_capacity(v___x_3966_);
                v___x_3968_ = lean_array_push(v___x_3967_, v_eType_3952_);
                v___x_3969_ = lean_array_push(v___x_3968_, v_targetType_3954_);
                v___x_3970_ = l_Lean_MessageData_ofLazyM(v___f_3965_, v___x_3969_);
                v___x_3971_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3971_, 0, v___x_3970_);
                v___x_3972_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_3961_,
                    v_mvarId_3951_,
                    v___x_3971_,
                    v_a_3956_,
                    v_a_3957_,
                    v_a_3958_,
                    v_a_3959_,
                );
                return v___x_3972_;
            }
            2 => {
                lean_inc_ref(v___y_3975_);
                v___x_3977_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3977_, 0, v___y_3975_);
                lean_ctor_set(v___x_3977_, 1, v___y_3976_);
                v___x_3978_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
                v___x_3979_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3979_, 0, v___x_3977_);
                lean_ctor_set(v___x_3979_, 1, v___x_3978_);
                lean_inc_ref(v_eType_3952_);
                v___x_3980_ = l_Lean_indentExpr(v_eType_3952_);
                v___x_3981_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3981_, 0, v___x_3979_);
                lean_ctor_set(v___x_3981_, 1, v___x_3980_);
                v___x_3982_ = l_Lean_MessageData_note(v___x_3981_);
                v___y_3963_ = v___y_3974_;
                v___y_3964_ = v___x_3982_;
                state = 1;
                continue;
            }
            3 => {
                if lean_obj_tag(v_conclusionType_x3f_3953_) == 0 {
                    v___x_3985_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
                    v___y_3963_ = v___y_3984_;
                    v___y_3964_ = v___x_3985_;
                    state = 1;
                    continue;
                } else {
                    v___x_3986_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
                    if lean_obj_tag(v_term_x3f_3955_) == 0 {
                        v___x_3987_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
                        v___y_3974_ = v___y_3984_;
                        v___y_3975_ = v___x_3986_;
                        v___y_3976_ = v___x_3987_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3988_ = lean_ctor_get(v_term_x3f_3955_, 0);
                        lean_inc(v_val_3988_);
                        v___y_3974_ = v___y_3984_;
                        v___y_3975_ = v___x_3986_;
                        v___y_3976_ = v_val_3988_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(
    mut v_mvarId_3990_: *mut LeanObject,
    mut v_eType_3991_: *mut LeanObject,
    mut v_conclusionType_x3f_3992_: *mut LeanObject,
    mut v_targetType_3993_: *mut LeanObject,
    mut v_term_x3f_3994_: *mut LeanObject,
    mut v_a_3995_: *mut LeanObject,
    mut v_a_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
    mut v_a_3999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4000_: *mut LeanObject = core::ptr::null_mut();
    v_res_4000_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(
        v_mvarId_3990_,
        v_eType_3991_,
        v_conclusionType_x3f_3992_,
        v_targetType_3993_,
        v_term_x3f_3994_,
        v_a_3995_,
        v_a_3996_,
        v_a_3997_,
        v_a_3998_,
    );
    lean_dec(v_a_3998_);
    lean_dec_ref(v_a_3997_);
    lean_dec(v_a_3996_);
    lean_dec_ref(v_a_3995_);
    return v_res_4000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(
    mut v_00_u03b1_4001_: *mut LeanObject,
    mut v_mvarId_4002_: *mut LeanObject,
    mut v_eType_4003_: *mut LeanObject,
    mut v_conclusionType_x3f_4004_: *mut LeanObject,
    mut v_targetType_4005_: *mut LeanObject,
    mut v_term_x3f_4006_: *mut LeanObject,
    mut v_a_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
    mut v_a_4009_: *mut LeanObject,
    mut v_a_4010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    v___x_4012_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(
        v_mvarId_4002_,
        v_eType_4003_,
        v_conclusionType_x3f_4004_,
        v_targetType_4005_,
        v_term_x3f_4006_,
        v_a_4007_,
        v_a_4008_,
        v_a_4009_,
        v_a_4010_,
    );
    return v___x_4012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(
    mut v_00_u03b1_4013_: *mut LeanObject,
    mut v_mvarId_4014_: *mut LeanObject,
    mut v_eType_4015_: *mut LeanObject,
    mut v_conclusionType_x3f_4016_: *mut LeanObject,
    mut v_targetType_4017_: *mut LeanObject,
    mut v_term_x3f_4018_: *mut LeanObject,
    mut v_a_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
    mut v_a_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4024_: *mut LeanObject = core::ptr::null_mut();
    v_res_4024_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(
        v_00_u03b1_4013_,
        v_mvarId_4014_,
        v_eType_4015_,
        v_conclusionType_x3f_4016_,
        v_targetType_4017_,
        v_term_x3f_4018_,
        v_a_4019_,
        v_a_4020_,
        v_a_4021_,
        v_a_4022_,
    );
    lean_dec(v_a_4022_);
    lean_dec_ref(v_a_4021_);
    lean_dec(v_a_4020_);
    lean_dec_ref(v_a_4019_);
    return v_res_4024_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(
    mut v_a_4025_: *mut LeanObject,
    mut v_snd_4026_: *mut LeanObject,
    mut v_fst_4027_: *mut LeanObject,
    mut v_____r_4028_: *mut LeanObject,
    mut v_progressAfterEx_4029_: u8,
    mut v___y_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    v___x_4035_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4035_, 0, v_a_4025_);
    v___x_4036_ = lean_box((v_progressAfterEx_4029_) as usize);
    v___x_4037_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4037_, 0, v___x_4036_);
    lean_ctor_set(v___x_4037_, 1, v_snd_4026_);
    v___x_4038_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4038_, 0, v_fst_4027_);
    lean_ctor_set(v___x_4038_, 1, v___x_4037_);
    v___x_4039_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4039_, 0, v___x_4035_);
    lean_ctor_set(v___x_4039_, 1, v___x_4038_);
    v___x_4040_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4040_, 0, v___x_4039_);
    return v___x_4040_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(
    mut v_a_4041_: *mut LeanObject,
    mut v_snd_4042_: *mut LeanObject,
    mut v_fst_4043_: *mut LeanObject,
    mut v_____r_4044_: *mut LeanObject,
    mut v_progressAfterEx_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_progressAfterEx_boxed_4051_: u8 = 0;
    let mut v_res_4052_: *mut LeanObject = core::ptr::null_mut();
    v_progressAfterEx_boxed_4051_ = (lean_unbox(v_progressAfterEx_4045_) as u8);
    v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_4041_, v_snd_4042_, v_fst_4043_, v_____r_4044_, v_progressAfterEx_boxed_4051_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
    lean_dec(v___y_4049_);
    lean_dec_ref(v___y_4048_);
    lean_dec(v___y_4047_);
    lean_dec_ref(v___y_4046_);
    return v_res_4052_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1;
    v___x_4057_ = l_Lean_MessageData_ofFormat(v___x_4056_);
    return v___x_4057_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    v___x_4058_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
    v___x_4059_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4059_, 0, v___x_4058_);
    return v___x_4059_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(
    mut v_allowSynthFailures_4060_: u8,
    mut v_tacticName_4061_: *mut LeanObject,
    mut v_mvarId_4062_: *mut LeanObject,
    mut v_as_4063_: *mut LeanObject,
    mut v_sz_4064_: usize,
    mut v_i_4065_: usize,
    mut v_b_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
    mut v___y_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: usize = 0;
    let mut v_fst_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u8 = 0;
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v_fst_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: u8 = 0;
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___y_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v_fst_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v_val_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4161_: u8 = 0;
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut v_isSharedCheck_4163_: u8 = 0;
    let mut v_unused_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: u8 = 0;
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_a_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4083_ = lean_usize_dec_lt(v_i_4065_, v_sz_4064_);
                if v___x_4083_ == 0 {
                    lean_dec(v_mvarId_4062_);
                    lean_dec(v_tacticName_4061_);
                    v___x_4084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4084_, 0, v_b_4066_);
                    return v___x_4084_;
                } else {
                    v_a_4085_ = lean_array_uget_borrowed(v_as_4063_, v_i_4065_);
                    lean_inc(v___y_4070_);
                    lean_inc_ref(v___y_4069_);
                    lean_inc(v___y_4068_);
                    lean_inc_ref(v___y_4067_);
                    lean_inc(v_a_4085_);
                    v___x_4086_ = lean_infer_type(
                        v_a_4085_,
                        v___y_4067_,
                        v___y_4068_,
                        v___y_4069_,
                        v___y_4070_,
                    );
                    if lean_obj_tag(v___x_4086_) == 0 {
                        v_snd_4087_ = lean_ctor_get(v_b_4066_, 1);
                        lean_inc(v_snd_4087_);
                        v_a_4088_ = lean_ctor_get(v___x_4086_, 0);
                        v_isSharedCheck_4181_ = (!lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4181_ == 0 {
                            v___x_4090_ = v___x_4086_;
                            v_isShared_4091_ = v_isSharedCheck_4181_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4088_);
                            lean_dec(v___x_4086_);
                            v___x_4090_ = lean_box(0);
                            v_isShared_4091_ = v_isSharedCheck_4181_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_4066_);
                        lean_dec(v_mvarId_4062_);
                        lean_dec(v_tacticName_4061_);
                        v_a_4182_ = lean_ctor_get(v___x_4086_, 0);
                        v_isSharedCheck_4189_ = (!lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4189_ == 0 {
                            v___x_4184_ = v___x_4086_;
                            v_isShared_4185_ = v_isSharedCheck_4189_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_4182_);
                            lean_dec(v___x_4086_);
                            v___x_4184_ = lean_box(0);
                            v_isShared_4185_ = v_isSharedCheck_4189_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4074_ = 1usize;
                v___x_4075_ = lean_usize_add(v_i_4065_, v___x_4074_);
                v_i_4065_ = v___x_4075_;
                v_b_4066_ = v_a_4073_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4081_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4081_, 0, v_fst_4079_);
                lean_ctor_set(v___x_4081_, 1, v_snd_4080_);
                v___x_4082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4082_, 0, v_fst_4078_);
                lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                v_a_4073_ = v___x_4082_;
                state = 1;
                continue;
            }
            3 => {
                v_fst_4092_ = lean_ctor_get(v_b_4066_, 0);
                lean_inc(v_fst_4092_);
                lean_dec_ref(v_b_4066_);
                v_fst_4093_ = lean_ctor_get(v_snd_4087_, 0);
                lean_inc(v_fst_4093_);
                v_snd_4094_ = lean_ctor_get(v_snd_4087_, 1);
                lean_inc(v_snd_4094_);
                lean_dec(v_snd_4087_);
                v___x_4169_ = lean_box(0);
                v___x_4170_ = l_Lean_Meta_synthInstance(
                    v_a_4088_,
                    v___x_4169_,
                    v___y_4067_,
                    v___y_4068_,
                    v___y_4069_,
                    v___y_4070_,
                );
                if lean_obj_tag(v___x_4170_) == 0 {
                    v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
                    lean_inc(v_a_4171_);
                    lean_dec_ref_known(v___x_4170_, 1);
                    v___x_4172_ = lean_array_get_size(v_snd_4094_);
                    v___x_4173_ = lean_unsigned_to_nat(0);
                    v___x_4174_ = lean_nat_dec_eq(v___x_4172_, v___x_4173_);
                    if v___x_4174_ == 0 {
                        v___x_4175_ = lean_box(0);
                        lean_inc(v_snd_4094_);
                        v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_4171_, v_snd_4094_, v_fst_4092_, v___x_4175_, v___x_4083_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
                        v___y_4108_ = v___x_4176_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4177_ = lean_box(0);
                        v___x_4178_ = (lean_unbox(v_fst_4093_) as u8);
                        lean_inc(v_snd_4094_);
                        v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_4171_, v_snd_4094_, v_fst_4092_, v___x_4177_, v___x_4178_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
                        v___y_4108_ = v___x_4179_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_4092_);
                    v_a_4180_ = lean_ctor_get(v___x_4170_, 0);
                    lean_inc(v_a_4180_);
                    lean_dec_ref_known(v___x_4170_, 1);
                    v_a_4104_ = v_a_4180_;
                    state = 6;
                    continue;
                }
            }
            4 => {
                if v___y_4097_ == 0 {
                    lean_del_object(v___x_4090_);
                    v___x_4098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4098_, 0, v___y_4096_);
                    lean_inc(v_a_4085_);
                    v___x_4099_ = lean_array_push(v_snd_4094_, v_a_4085_);
                    v_fst_4078_ = v___x_4098_;
                    v_fst_4079_ = v_fst_4093_;
                    v_snd_4080_ = v___x_4099_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_4094_);
                    lean_dec(v_fst_4093_);
                    lean_dec(v_mvarId_4062_);
                    lean_dec(v_tacticName_4061_);
                    if v_isShared_4091_ == 0 {
                        lean_ctor_set_tag(v___x_4090_, 1);
                        lean_ctor_set(v___x_4090_, 0, v___y_4096_);
                        v___x_4101_ = v___x_4090_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___y_4096_);
                        v___x_4101_ = v_reuseFailAlloc_4102_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4101_;
            }
            6 => {
                v___x_4105_ = l_Lean_Exception_isInterrupt(v_a_4104_);
                if v___x_4105_ == 0 {
                    lean_inc_ref(v_a_4104_);
                    v___x_4106_ = l_Lean_Exception_isRuntime(v_a_4104_);
                    v___y_4096_ = v_a_4104_;
                    v___y_4097_ = v___x_4106_;
                    state = 4;
                    continue;
                } else {
                    v___y_4096_ = v_a_4104_;
                    v___y_4097_ = v___x_4105_;
                    state = 4;
                    continue;
                }
            }
            7 => {
                if lean_obj_tag(v___y_4108_) == 0 {
                    lean_dec(v_snd_4094_);
                    lean_dec(v_fst_4093_);
                    lean_del_object(v___x_4090_);
                    v_a_4109_ = lean_ctor_get(v___y_4108_, 0);
                    lean_inc(v_a_4109_);
                    lean_dec_ref_known(v___y_4108_, 1);
                    v_snd_4110_ = lean_ctor_get(v_a_4109_, 1);
                    lean_inc(v_snd_4110_);
                    v_snd_4111_ = lean_ctor_get(v_snd_4110_, 1);
                    lean_inc(v_snd_4111_);
                    v_fst_4112_ = lean_ctor_get(v_a_4109_, 0);
                    lean_inc(v_fst_4112_);
                    lean_dec(v_a_4109_);
                    if lean_obj_tag(v_fst_4112_) == 1 {
                        v_fst_4113_ = lean_ctor_get(v_snd_4110_, 0);
                        v_isSharedCheck_4163_ = (!lean_is_exclusive(v_snd_4110_)) as u8;
                        if v_isSharedCheck_4163_ == 0 {
                            v_unused_4164_ = lean_ctor_get(v_snd_4110_, 1);
                            lean_dec(v_unused_4164_);
                            v___x_4115_ = v_snd_4110_;
                            v_isShared_4116_ = v_isSharedCheck_4163_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_fst_4113_);
                            lean_dec(v_snd_4110_);
                            v___x_4115_ = lean_box(0);
                            v_isShared_4116_ = v_isSharedCheck_4163_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_4112_);
                        v_fst_4165_ = lean_ctor_get(v_snd_4110_, 0);
                        lean_inc(v_fst_4165_);
                        lean_dec(v_snd_4110_);
                        v_fst_4166_ = lean_ctor_get(v_snd_4111_, 0);
                        lean_inc(v_fst_4166_);
                        v_snd_4167_ = lean_ctor_get(v_snd_4111_, 1);
                        lean_inc(v_snd_4167_);
                        lean_dec(v_snd_4111_);
                        v_fst_4078_ = v_fst_4165_;
                        v_fst_4079_ = v_fst_4166_;
                        v_snd_4080_ = v_snd_4167_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4168_ = lean_ctor_get(v___y_4108_, 0);
                    lean_inc(v_a_4168_);
                    lean_dec_ref_known(v___y_4108_, 1);
                    v_a_4104_ = v_a_4168_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v_fst_4117_ = lean_ctor_get(v_snd_4111_, 0);
                v_snd_4118_ = lean_ctor_get(v_snd_4111_, 1);
                v_isSharedCheck_4162_ = (!lean_is_exclusive(v_snd_4111_)) as u8;
                if v_isSharedCheck_4162_ == 0 {
                    v___x_4120_ = v_snd_4111_;
                    v_isShared_4121_ = v_isSharedCheck_4162_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_snd_4118_);
                    lean_inc(v_fst_4117_);
                    lean_dec(v_snd_4111_);
                    v___x_4120_ = lean_box(0);
                    v_isShared_4121_ = v_isSharedCheck_4162_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_val_4122_ = lean_ctor_get(v_fst_4112_, 0);
                lean_inc(v_val_4122_);
                lean_dec_ref_known(v_fst_4112_, 1);
                lean_inc(v_a_4085_);
                v___x_4123_ = l_Lean_Meta_isExprDefEq(
                    v_a_4085_,
                    v_val_4122_,
                    v___y_4067_,
                    v___y_4068_,
                    v___y_4069_,
                    v___y_4070_,
                );
                if lean_obj_tag(v___x_4123_) == 0 {
                    v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
                    lean_inc(v_a_4124_);
                    lean_dec_ref_known(v___x_4123_, 1);
                    v___x_4125_ = (lean_unbox(v_a_4124_) as u8);
                    lean_dec(v_a_4124_);
                    if v___x_4125_ == 0 {
                        if v_allowSynthFailures_4060_ == 0 {
                            v___x_4126_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
                            lean_inc(v_mvarId_4062_);
                            lean_inc(v_tacticName_4061_);
                            v___x_4127_ = l_Lean_Meta_throwTacticEx___redArg(
                                v_tacticName_4061_,
                                v_mvarId_4062_,
                                v___x_4126_,
                                v___y_4067_,
                                v___y_4068_,
                                v___y_4069_,
                                v___y_4070_,
                            );
                            if lean_obj_tag(v___x_4127_) == 0 {
                                lean_dec_ref_known(v___x_4127_, 1);
                                if v_isShared_4121_ == 0 {
                                    v___x_4129_ = v___x_4120_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_fst_4117_);
                                    lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_snd_4118_);
                                    v___x_4129_ = v_reuseFailAlloc_4133_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_4120_);
                                lean_dec(v_snd_4118_);
                                lean_dec(v_fst_4117_);
                                lean_del_object(v___x_4115_);
                                lean_dec(v_fst_4113_);
                                lean_dec(v_mvarId_4062_);
                                lean_dec(v_tacticName_4061_);
                                v_a_4134_ = lean_ctor_get(v___x_4127_, 0);
                                v_isSharedCheck_4141_ = (!lean_is_exclusive(v___x_4127_)) as u8;
                                if v_isSharedCheck_4141_ == 0 {
                                    v___x_4136_ = v___x_4127_;
                                    v_isShared_4137_ = v_isSharedCheck_4141_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_4134_);
                                    lean_dec(v___x_4127_);
                                    v___x_4136_ = lean_box(0);
                                    v_isShared_4137_ = v_isSharedCheck_4141_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            if v_isShared_4121_ == 0 {
                                v___x_4143_ = v___x_4120_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_fst_4117_);
                                lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_snd_4118_);
                                v___x_4143_ = v_reuseFailAlloc_4147_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        if v_isShared_4121_ == 0 {
                            v___x_4149_ = v___x_4120_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_fst_4117_);
                            lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_snd_4118_);
                            v___x_4149_ = v_reuseFailAlloc_4153_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4120_);
                    lean_dec(v_snd_4118_);
                    lean_dec(v_fst_4117_);
                    lean_del_object(v___x_4115_);
                    lean_dec(v_fst_4113_);
                    lean_dec(v_mvarId_4062_);
                    lean_dec(v_tacticName_4061_);
                    v_a_4154_ = lean_ctor_get(v___x_4123_, 0);
                    v_isSharedCheck_4161_ = (!lean_is_exclusive(v___x_4123_)) as u8;
                    if v_isSharedCheck_4161_ == 0 {
                        v___x_4156_ = v___x_4123_;
                        v_isShared_4157_ = v_isSharedCheck_4161_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_4154_);
                        lean_dec(v___x_4123_);
                        v___x_4156_ = lean_box(0);
                        v_isShared_4157_ = v_isSharedCheck_4161_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4116_ == 0 {
                    lean_ctor_set(v___x_4115_, 1, v___x_4129_);
                    v___x_4131_ = v___x_4115_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_fst_4113_);
                    lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4129_);
                    v___x_4131_ = v_reuseFailAlloc_4132_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_4073_ = v___x_4131_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4137_ == 0 {
                    v___x_4139_ = v___x_4136_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4139_;
            }
            14 => {
                if v_isShared_4116_ == 0 {
                    lean_ctor_set(v___x_4115_, 1, v___x_4143_);
                    v___x_4145_ = v___x_4115_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_fst_4113_);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4143_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_a_4073_ = v___x_4145_;
                state = 1;
                continue;
            }
            16 => {
                if v_isShared_4116_ == 0 {
                    lean_ctor_set(v___x_4115_, 1, v___x_4149_);
                    v___x_4151_ = v___x_4115_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_fst_4113_);
                    lean_ctor_set(v_reuseFailAlloc_4152_, 1, v___x_4149_);
                    v___x_4151_ = v_reuseFailAlloc_4152_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v_a_4073_ = v___x_4151_;
                state = 1;
                continue;
            }
            18 => {
                if v_isShared_4157_ == 0 {
                    v___x_4159_ = v___x_4156_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
                    v___x_4159_ = v_reuseFailAlloc_4160_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4159_;
            }
            20 => {
                if v_isShared_4185_ == 0 {
                    v___x_4187_ = v___x_4184_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
                    v___x_4187_ = v_reuseFailAlloc_4188_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(
    mut v_allowSynthFailures_4190_: *mut LeanObject,
    mut v_tacticName_4191_: *mut LeanObject,
    mut v_mvarId_4192_: *mut LeanObject,
    mut v_as_4193_: *mut LeanObject,
    mut v_sz_4194_: *mut LeanObject,
    mut v_i_4195_: *mut LeanObject,
    mut v_b_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowSynthFailures_boxed_4202_: u8 = 0;
    let mut v_sz_boxed_4203_: usize = 0;
    let mut v_i_boxed_4204_: usize = 0;
    let mut v_res_4205_: *mut LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4202_ = (lean_unbox(v_allowSynthFailures_4190_) as u8);
    v_sz_boxed_4203_ = lean_unbox_usize(v_sz_4194_);
    lean_dec(v_sz_4194_);
    v_i_boxed_4204_ = lean_unbox_usize(v_i_4195_);
    lean_dec(v_i_4195_);
    v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_4202_, v_tacticName_4191_, v_mvarId_4192_, v_as_4193_, v_sz_boxed_4203_, v_i_boxed_4204_, v_b_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    lean_dec(v___y_4200_);
    lean_dec_ref(v___y_4199_);
    lean_dec(v___y_4198_);
    lean_dec_ref(v___y_4197_);
    lean_dec_ref(v_as_4193_);
    return v_res_4205_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(
    mut v_tacticName_4215_: *mut LeanObject,
    mut v_mvarId_4216_: *mut LeanObject,
    mut v_allowSynthFailures_4217_: u8,
    mut v_mvars_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
    mut v_a_4221_: *mut LeanObject,
    mut v_a_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_postponed_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4226_: usize = 0;
    let mut v___x_4227_: usize = 0;
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v_fst_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v_val_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_a_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_postponed_4224_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0;
                v___x_4225_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2;
                v_sz_4226_ = lean_array_size(v_mvars_4218_);
                v___x_4227_ = 0usize;
                v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_4217_, v_tacticName_4215_, v_mvarId_4216_, v_mvars_4218_, v_sz_4226_, v___x_4227_, v___x_4225_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
                if lean_obj_tag(v___x_4228_) == 0 {
                    v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
                    v_isSharedCheck_4251_ = (!lean_is_exclusive(v___x_4228_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4231_ = v___x_4228_;
                        v_isShared_4232_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4229_);
                        lean_dec(v___x_4228_);
                        v___x_4231_ = lean_box(0);
                        v_isShared_4232_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4252_ = lean_ctor_get(v___x_4228_, 0);
                    v_isSharedCheck_4259_ = (!lean_is_exclusive(v___x_4228_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4228_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4252_);
                        lean_dec(v___x_4228_);
                        v___x_4254_ = lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4233_ = lean_ctor_get(v_a_4229_, 0);
                lean_inc(v_fst_4233_);
                if lean_obj_tag(v_fst_4233_) == 1 {
                    v_snd_4234_ = lean_ctor_get(v_a_4229_, 1);
                    lean_inc(v_snd_4234_);
                    lean_dec(v_a_4229_);
                    v_fst_4235_ = lean_ctor_get(v_snd_4234_, 0);
                    v___x_4236_ = (lean_unbox(v_fst_4235_) as u8);
                    if v___x_4236_ == 0 {
                        lean_dec(v_snd_4234_);
                        if v_allowSynthFailures_4217_ == 0 {
                            v_val_4237_ = lean_ctor_get(v_fst_4233_, 0);
                            lean_inc(v_val_4237_);
                            lean_dec_ref_known(v_fst_4233_, 1);
                            if v_isShared_4232_ == 0 {
                                lean_ctor_set_tag(v___x_4231_, 1);
                                lean_ctor_set(v___x_4231_, 0, v_val_4237_);
                                v___x_4239_ = v___x_4231_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_val_4237_);
                                v___x_4239_ = v_reuseFailAlloc_4240_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_fst_4233_, 1);
                            if v_isShared_4232_ == 0 {
                                lean_ctor_set(v___x_4231_, 0, v_postponed_4224_);
                                v___x_4242_ = v___x_4231_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_postponed_4224_);
                                v___x_4242_ = v_reuseFailAlloc_4243_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_fst_4233_, 1);
                        v_snd_4244_ = lean_ctor_get(v_snd_4234_, 1);
                        lean_inc(v_snd_4244_);
                        lean_dec(v_snd_4234_);
                        if v_isShared_4232_ == 0 {
                            lean_ctor_set(v___x_4231_, 0, v_snd_4244_);
                            v___x_4246_ = v___x_4231_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_snd_4244_);
                            v___x_4246_ = v_reuseFailAlloc_4247_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_4233_);
                    lean_dec(v_a_4229_);
                    if v_isShared_4232_ == 0 {
                        lean_ctor_set(v___x_4231_, 0, v_postponed_4224_);
                        v___x_4249_ = v___x_4231_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_postponed_4224_);
                        v___x_4249_ = v_reuseFailAlloc_4250_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4239_;
            }
            3 => {
                return v___x_4242_;
            }
            4 => {
                return v___x_4246_;
            }
            5 => {
                return v___x_4249_;
            }
            6 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(
    mut v_tacticName_4260_: *mut LeanObject,
    mut v_mvarId_4261_: *mut LeanObject,
    mut v_allowSynthFailures_4262_: *mut LeanObject,
    mut v_mvars_4263_: *mut LeanObject,
    mut v_a_4264_: *mut LeanObject,
    mut v_a_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
    mut v_a_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowSynthFailures_boxed_4269_: u8 = 0;
    let mut v_res_4270_: *mut LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4269_ = (lean_unbox(v_allowSynthFailures_4262_) as u8);
    v_res_4270_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(
        v_tacticName_4260_,
        v_mvarId_4261_,
        v_allowSynthFailures_boxed_4269_,
        v_mvars_4263_,
        v_a_4264_,
        v_a_4265_,
        v_a_4266_,
        v_a_4267_,
    );
    lean_dec(v_a_4267_);
    lean_dec_ref(v_a_4266_);
    lean_dec(v_a_4265_);
    lean_dec_ref(v_a_4264_);
    lean_dec_ref(v_mvars_4263_);
    return v_res_4270_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_keys_4271_: *mut LeanObject,
    mut v_i_4272_: *mut LeanObject,
    mut v_k_4273_: *mut LeanObject,
) -> u8 {
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u8 = 0;
    let mut v_k_x27_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4274_ = lean_array_get_size(v_keys_4271_);
                v___x_4275_ = lean_nat_dec_lt(v_i_4272_, v___x_4274_);
                if v___x_4275_ == 0 {
                    lean_dec(v_i_4272_);
                    return v___x_4275_;
                } else {
                    v_k_x27_4276_ = lean_array_fget_borrowed(v_keys_4271_, v_i_4272_);
                    v___x_4277_ = l_Lean_instBEqMVarId_beq(v_k_4273_, v_k_x27_4276_);
                    if v___x_4277_ == 0 {
                        v___x_4278_ = lean_unsigned_to_nat(1);
                        v___x_4279_ = lean_nat_add(v_i_4272_, v___x_4278_);
                        lean_dec(v_i_4272_);
                        v_i_4272_ = v___x_4279_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4272_);
                        return v___x_4277_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_keys_4281_: *mut LeanObject,
    mut v_i_4282_: *mut LeanObject,
    mut v_k_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4284_: u8 = 0;
    let mut v_r_4285_: *mut LeanObject = core::ptr::null_mut();
    v_res_4284_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_4281_, v_i_4282_, v_k_4283_);
    lean_dec(v_k_4283_);
    lean_dec_ref(v_keys_4281_);
    v_r_4285_ = lean_box((v_res_4284_) as usize);
    return v_r_4285_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: usize = 0;
    let mut v___x_4288_: usize = 0;
    v___x_4286_ = 5usize;
    v___x_4287_ = 1usize;
    v___x_4288_ = lean_usize_shift_left(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_4289_: usize = 0;
    let mut v___x_4290_: usize = 0;
    let mut v___x_4291_: usize = 0;
    v___x_4289_ = 1usize;
    v___x_4290_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_4291_ = lean_usize_sub(v___x_4290_, v___x_4289_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(
    mut v_x_4292_: *mut LeanObject,
    mut v_x_4293_: usize,
    mut v_x_4294_: *mut LeanObject,
) -> u8 {
    let mut v_es_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: usize = 0;
    let mut v___x_4298_: usize = 0;
    let mut v___x_4299_: usize = 0;
    let mut v_j_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: u8 = 0;
    let mut v_node_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: usize = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v_ks_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4292_) == 0 {
                    v_es_4295_ = lean_ctor_get(v_x_4292_, 0);
                    v___x_4296_ = lean_box(2);
                    v___x_4297_ = 5usize;
                    v___x_4298_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4299_ = lean_usize_land(v_x_4293_, v___x_4298_);
                    v_j_4300_ = lean_usize_to_nat(v___x_4299_);
                    v___x_4301_ = lean_array_get_borrowed(v___x_4296_, v_es_4295_, v_j_4300_);
                    lean_dec(v_j_4300_);
                    match lean_obj_tag(v___x_4301_) {
                        0 => {
                            v_key_4302_ = lean_ctor_get(v___x_4301_, 0);
                            v___x_4303_ = l_Lean_instBEqMVarId_beq(v_x_4294_, v_key_4302_);
                            return v___x_4303_;
                        }
                        1 => {
                            v_node_4304_ = lean_ctor_get(v___x_4301_, 0);
                            v___x_4305_ = lean_usize_shift_right(v_x_4293_, v___x_4297_);
                            v_x_4292_ = v_node_4304_;
                            v_x_4293_ = v___x_4305_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4307_ = 0;
                            return v___x_4307_;
                        }
                    }
                } else {
                    v_ks_4308_ = lean_ctor_get(v_x_4292_, 0);
                    v___x_4309_ = lean_unsigned_to_nat(0);
                    v___x_4310_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_4308_, v___x_4309_, v_x_4294_);
                    return v___x_4310_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4311_: *mut LeanObject,
    mut v_x_4312_: *mut LeanObject,
    mut v_x_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3030__boxed_4314_: usize = 0;
    let mut v_res_4315_: u8 = 0;
    let mut v_r_4316_: *mut LeanObject = core::ptr::null_mut();
    v_x_3030__boxed_4314_ = lean_unbox_usize(v_x_4312_);
    lean_dec(v_x_4312_);
    v_res_4315_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_4311_, v_x_3030__boxed_4314_, v_x_4313_);
    lean_dec(v_x_4313_);
    lean_dec_ref(v_x_4311_);
    v_r_4316_ = lean_box((v_res_4315_) as usize);
    return v_r_4316_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(
    mut v_x_4317_: *mut LeanObject,
    mut v_x_4318_: *mut LeanObject,
) -> u8 {
    let mut v___x_4319_: u64 = 0;
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: u8 = 0;
    v___x_4319_ = l_Lean_instHashableMVarId_hash(v_x_4318_);
    v___x_4320_ = lean_uint64_to_usize(v___x_4319_);
    v___x_4321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_4317_, v___x_4320_, v_x_4318_);
    return v___x_4321_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(
    mut v_x_4322_: *mut LeanObject,
    mut v_x_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4324_: u8 = 0;
    let mut v_r_4325_: *mut LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_4322_, v_x_4323_);
    lean_dec(v_x_4323_);
    lean_dec_ref(v_x_4322_);
    v_r_4325_ = lean_box((v_res_4324_) as usize);
    return v_r_4325_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(
    mut v_mvarId_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    v___x_4329_ = lean_st_ref_get(v___y_4327_);
    v_mctx_4330_ = lean_ctor_get(v___x_4329_, 0);
    lean_inc_ref(v_mctx_4330_);
    lean_dec(v___x_4329_);
    v_eAssignment_4331_ = lean_ctor_get(v_mctx_4330_, 8);
    lean_inc_ref(v_eAssignment_4331_);
    lean_dec_ref(v_mctx_4330_);
    v___x_4332_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_4331_, v_mvarId_4326_);
    lean_dec_ref(v_eAssignment_4331_);
    v___x_4333_ = lean_box((v___x_4332_) as usize);
    v___x_4334_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4334_, 0, v___x_4333_);
    return v___x_4334_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(
    mut v_mvarId_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4338_: *mut LeanObject = core::ptr::null_mut();
    v_res_4338_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(
        v_mvarId_4335_,
        v___y_4336_,
    );
    lean_dec(v___y_4336_);
    lean_dec(v_mvarId_4335_);
    return v_res_4338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(
    mut v_synthAssignedInstances_4339_: u8,
    mut v_as_4340_: *mut LeanObject,
    mut v_sz_4341_: usize,
    mut v_i_4342_: usize,
    mut v_b_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: usize = 0;
    let mut v___x_4352_: usize = 0;
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v_array_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4371_: u8 = 0;
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v_a_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4397_: u8 = 0;
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v_reuseFailAlloc_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4403_: u8 = 0;
    let mut v_unused_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4354_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
                if v___x_4354_ == 0 {
                    v___x_4355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4355_, 0, v_b_4343_);
                    return v___x_4355_;
                } else {
                    v_snd_4356_ = lean_ctor_get(v_b_4343_, 1);
                    v_fst_4357_ = lean_ctor_get(v_b_4343_, 0);
                    v_isSharedCheck_4407_ = (!lean_is_exclusive(v_b_4343_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v___x_4359_ = v_b_4343_;
                        v_isShared_4360_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4356_);
                        lean_inc(v_fst_4357_);
                        lean_dec(v_b_4343_);
                        v___x_4359_ = lean_box(0);
                        v_isShared_4360_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4351_ = 1usize;
                v___x_4352_ = lean_usize_add(v_i_4342_, v___x_4351_);
                v_i_4342_ = v___x_4352_;
                v_b_4343_ = v_a_4350_;
                state = 0;
                continue;
            }
            2 => {
                v_array_4361_ = lean_ctor_get(v_snd_4356_, 0);
                v_start_4362_ = lean_ctor_get(v_snd_4356_, 1);
                v_stop_4363_ = lean_ctor_get(v_snd_4356_, 2);
                v___x_4364_ = lean_nat_dec_lt(v_start_4362_, v_stop_4363_);
                if v___x_4364_ == 0 {
                    if v_isShared_4360_ == 0 {
                        v___x_4366_ = v___x_4359_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_fst_4357_);
                        lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_snd_4356_);
                        v___x_4366_ = v_reuseFailAlloc_4368_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_4363_);
                    lean_inc(v_start_4362_);
                    lean_inc_ref(v_array_4361_);
                    v_isSharedCheck_4403_ = (!lean_is_exclusive(v_snd_4356_)) as u8;
                    if v_isSharedCheck_4403_ == 0 {
                        v_unused_4404_ = lean_ctor_get(v_snd_4356_, 2);
                        lean_dec(v_unused_4404_);
                        v_unused_4405_ = lean_ctor_get(v_snd_4356_, 1);
                        lean_dec(v_unused_4405_);
                        v_unused_4406_ = lean_ctor_get(v_snd_4356_, 0);
                        lean_dec(v_unused_4406_);
                        v___x_4370_ = v_snd_4356_;
                        v_isShared_4371_ = v_isSharedCheck_4403_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_4356_);
                        v___x_4370_ = lean_box(0);
                        v_isShared_4371_ = v_isSharedCheck_4403_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4367_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4367_, 0, v___x_4366_);
                return v___x_4367_;
            }
            4 => {
                v___x_4372_ = lean_array_fget(v_array_4361_, v_start_4362_);
                v___x_4373_ = lean_unsigned_to_nat(1);
                v___x_4374_ = lean_nat_add(v_start_4362_, v___x_4373_);
                lean_dec(v_start_4362_);
                if v_isShared_4371_ == 0 {
                    lean_ctor_set(v___x_4370_, 1, v___x_4374_);
                    v___x_4376_ = v___x_4370_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_array_4361_);
                    lean_ctor_set(v_reuseFailAlloc_4402_, 1, v___x_4374_);
                    lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_stop_4363_);
                    v___x_4376_ = v_reuseFailAlloc_4402_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4377_ = (lean_unbox(v___x_4372_) as u8);
                lean_dec(v___x_4372_);
                v___x_4378_ = l_Lean_BinderInfo_isInstImplicit(v___x_4377_);
                if v___x_4378_ == 0 {
                    if v_isShared_4360_ == 0 {
                        lean_ctor_set(v___x_4359_, 1, v___x_4376_);
                        v___x_4380_ = v___x_4359_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_fst_4357_);
                        lean_ctor_set(v_reuseFailAlloc_4381_, 1, v___x_4376_);
                        v___x_4380_ = v_reuseFailAlloc_4381_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_4382_ = lean_array_uget_borrowed(v_as_4340_, v_i_4342_);
                    v___x_4383_ = l_Lean_Expr_mvarId_x21(v_a_4382_);
                    v___x_4384_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_4383_, v___y_4345_);
                    lean_dec(v___x_4383_);
                    if lean_obj_tag(v___x_4384_) == 0 {
                        v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
                        lean_inc(v_a_4385_);
                        lean_dec_ref_known(v___x_4384_, 1);
                        if v_synthAssignedInstances_4339_ == 0 {
                            v___x_4393_ = (lean_unbox(v_a_4385_) as u8);
                            lean_dec(v_a_4385_);
                            if v___x_4393_ == 0 {
                                if v___x_4378_ == 0 {
                                    state = 7;
                                    continue;
                                } else {
                                    lean_del_object(v___x_4359_);
                                    state = 9;
                                    continue;
                                }
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4385_);
                            lean_del_object(v___x_4359_);
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4376_);
                        lean_del_object(v___x_4359_);
                        lean_dec(v_fst_4357_);
                        v_a_4394_ = lean_ctor_get(v___x_4384_, 0);
                        v_isSharedCheck_4401_ = (!lean_is_exclusive(v___x_4384_)) as u8;
                        if v_isSharedCheck_4401_ == 0 {
                            v___x_4396_ = v___x_4384_;
                            v_isShared_4397_ = v_isSharedCheck_4401_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4394_);
                            lean_dec(v___x_4384_);
                            v___x_4396_ = lean_box(0);
                            v_isShared_4397_ = v_isSharedCheck_4401_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v_a_4350_ = v___x_4380_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_4360_ == 0 {
                    lean_ctor_set(v___x_4359_, 1, v___x_4376_);
                    v___x_4388_ = v___x_4359_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_fst_4357_);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 1, v___x_4376_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_4350_ = v___x_4388_;
                state = 1;
                continue;
            }
            9 => {
                lean_inc(v_a_4382_);
                v___x_4391_ = lean_array_push(v_fst_4357_, v_a_4382_);
                v___x_4392_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4392_, 0, v___x_4391_);
                lean_ctor_set(v___x_4392_, 1, v___x_4376_);
                v_a_4350_ = v___x_4392_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4397_ == 0 {
                    v___x_4399_ = v___x_4396_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
                    v___x_4399_ = v_reuseFailAlloc_4400_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(
    mut v_synthAssignedInstances_4408_: *mut LeanObject,
    mut v_as_4409_: *mut LeanObject,
    mut v_sz_4410_: *mut LeanObject,
    mut v_i_4411_: *mut LeanObject,
    mut v_b_4412_: *mut LeanObject,
    mut v___y_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
    mut v___y_4416_: *mut LeanObject,
    mut v___y_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthAssignedInstances_boxed_4418_: u8 = 0;
    let mut v_sz_boxed_4419_: usize = 0;
    let mut v_i_boxed_4420_: usize = 0;
    let mut v_res_4421_: *mut LeanObject = core::ptr::null_mut();
    v_synthAssignedInstances_boxed_4418_ = (lean_unbox(v_synthAssignedInstances_4408_) as u8);
    v_sz_boxed_4419_ = lean_unbox_usize(v_sz_4410_);
    lean_dec(v_sz_4410_);
    v_i_boxed_4420_ = lean_unbox_usize(v_i_4411_);
    lean_dec(v_i_4411_);
    v_res_4421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_4418_, v_as_4409_, v_sz_boxed_4419_, v_i_boxed_4420_, v_b_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
    lean_dec(v___y_4416_);
    lean_dec_ref(v___y_4415_);
    lean_dec(v___y_4414_);
    lean_dec_ref(v___y_4413_);
    lean_dec_ref(v_as_4409_);
    return v_res_4421_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(
    mut v_tacticName_4422_: *mut LeanObject,
    mut v_mvarId_4423_: *mut LeanObject,
    mut v_allowSynthFailures_4424_: u8,
    mut v_a_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4431_ = lean_array_get_size(v_a_4425_);
                v___x_4432_ = lean_unsigned_to_nat(0);
                v___x_4433_ = lean_nat_dec_eq(v___x_4431_, v___x_4432_);
                if v___x_4433_ == 0 {
                    lean_inc(v_mvarId_4423_);
                    lean_inc(v_tacticName_4422_);
                    v___x_4434_ =
                        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(
                            v_tacticName_4422_,
                            v_mvarId_4423_,
                            v_allowSynthFailures_4424_,
                            v_a_4425_,
                            v___y_4426_,
                            v___y_4427_,
                            v___y_4428_,
                            v___y_4429_,
                        );
                    lean_dec_ref(v_a_4425_);
                    if lean_obj_tag(v___x_4434_) == 0 {
                        v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
                        lean_inc(v_a_4435_);
                        lean_dec_ref_known(v___x_4434_, 1);
                        v_a_4425_ = v_a_4435_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mvarId_4423_);
                        lean_dec(v_tacticName_4422_);
                        return v___x_4434_;
                    }
                } else {
                    lean_dec(v_mvarId_4423_);
                    lean_dec(v_tacticName_4422_);
                    v___x_4437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4437_, 0, v_a_4425_);
                    return v___x_4437_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(
    mut v_tacticName_4438_: *mut LeanObject,
    mut v_mvarId_4439_: *mut LeanObject,
    mut v_allowSynthFailures_4440_: *mut LeanObject,
    mut v_a_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowSynthFailures_boxed_4447_: u8 = 0;
    let mut v_res_4448_: *mut LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4447_ = (lean_unbox(v_allowSynthFailures_4440_) as u8);
    v_res_4448_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_4438_, v_mvarId_4439_, v_allowSynthFailures_boxed_4447_, v_a_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
    lean_dec(v___y_4445_);
    lean_dec_ref(v___y_4444_);
    lean_dec(v___y_4443_);
    lean_dec_ref(v___y_4442_);
    return v_res_4448_;
}
pub unsafe fn l_Lean_Meta_synthAppInstances(
    mut v_tacticName_4449_: *mut LeanObject,
    mut v_mvarId_4450_: *mut LeanObject,
    mut v_mvarsNew_4451_: *mut LeanObject,
    mut v_binderInfos_4452_: *mut LeanObject,
    mut v_synthAssignedInstances_4453_: u8,
    mut v_allowSynthFailures_4454_: u8,
    mut v_a_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_todo_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4465_: usize = 0;
    let mut v___x_4466_: usize = 0;
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4473_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_unused_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4460_ = lean_unsigned_to_nat(0);
                v_todo_4461_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0;
                v___x_4462_ = lean_array_get_size(v_binderInfos_4452_);
                v___x_4463_ =
                    l_Array_toSubarray___redArg(v_binderInfos_4452_, v___x_4460_, v___x_4462_);
                v___x_4464_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4464_, 0, v_todo_4461_);
                lean_ctor_set(v___x_4464_, 1, v___x_4463_);
                v_sz_4465_ = lean_array_size(v_mvarsNew_4451_);
                v___x_4466_ = 0usize;
                v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_4453_, v_mvarsNew_4451_, v_sz_4465_, v___x_4466_, v___x_4464_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
                if lean_obj_tag(v___x_4467_) == 0 {
                    v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
                    lean_inc(v_a_4468_);
                    lean_dec_ref_known(v___x_4467_, 1);
                    v_fst_4469_ = lean_ctor_get(v_a_4468_, 0);
                    lean_inc(v_fst_4469_);
                    lean_dec(v_a_4468_);
                    v___x_4470_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_4449_, v_mvarId_4450_, v_allowSynthFailures_4454_, v_fst_4469_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
                    if lean_obj_tag(v___x_4470_) == 0 {
                        v_isSharedCheck_4478_ = (!lean_is_exclusive(v___x_4470_)) as u8;
                        if v_isSharedCheck_4478_ == 0 {
                            v_unused_4479_ = lean_ctor_get(v___x_4470_, 0);
                            lean_dec(v_unused_4479_);
                            v___x_4472_ = v___x_4470_;
                            v_isShared_4473_ = v_isSharedCheck_4478_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4470_);
                            v___x_4472_ = lean_box(0);
                            v_isShared_4473_ = v_isSharedCheck_4478_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4480_ = lean_ctor_get(v___x_4470_, 0);
                        v_isSharedCheck_4487_ = (!lean_is_exclusive(v___x_4470_)) as u8;
                        if v_isSharedCheck_4487_ == 0 {
                            v___x_4482_ = v___x_4470_;
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4480_);
                            lean_dec(v___x_4470_);
                            v___x_4482_ = lean_box(0);
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_4450_);
                    lean_dec(v_tacticName_4449_);
                    v_a_4488_ = lean_ctor_get(v___x_4467_, 0);
                    v_isSharedCheck_4495_ = (!lean_is_exclusive(v___x_4467_)) as u8;
                    if v_isSharedCheck_4495_ == 0 {
                        v___x_4490_ = v___x_4467_;
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4488_);
                        lean_dec(v___x_4467_);
                        v___x_4490_ = lean_box(0);
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4474_ = lean_box(0);
                if v_isShared_4473_ == 0 {
                    lean_ctor_set(v___x_4472_, 0, v___x_4474_);
                    v___x_4476_ = v___x_4472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
                    v___x_4476_ = v_reuseFailAlloc_4477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4476_;
            }
            3 => {
                if v_isShared_4483_ == 0 {
                    v___x_4485_ = v___x_4482_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
                    v___x_4485_ = v_reuseFailAlloc_4486_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4485_;
            }
            5 => {
                if v_isShared_4491_ == 0 {
                    v___x_4493_ = v___x_4490_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_synthAppInstances___boxed(
    mut v_tacticName_4496_: *mut LeanObject,
    mut v_mvarId_4497_: *mut LeanObject,
    mut v_mvarsNew_4498_: *mut LeanObject,
    mut v_binderInfos_4499_: *mut LeanObject,
    mut v_synthAssignedInstances_4500_: *mut LeanObject,
    mut v_allowSynthFailures_4501_: *mut LeanObject,
    mut v_a_4502_: *mut LeanObject,
    mut v_a_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
    mut v_a_4505_: *mut LeanObject,
    mut v_a_4506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthAssignedInstances_boxed_4507_: u8 = 0;
    let mut v_allowSynthFailures_boxed_4508_: u8 = 0;
    let mut v_res_4509_: *mut LeanObject = core::ptr::null_mut();
    v_synthAssignedInstances_boxed_4507_ = (lean_unbox(v_synthAssignedInstances_4500_) as u8);
    v_allowSynthFailures_boxed_4508_ = (lean_unbox(v_allowSynthFailures_4501_) as u8);
    v_res_4509_ = l_Lean_Meta_synthAppInstances(
        v_tacticName_4496_,
        v_mvarId_4497_,
        v_mvarsNew_4498_,
        v_binderInfos_4499_,
        v_synthAssignedInstances_boxed_4507_,
        v_allowSynthFailures_boxed_4508_,
        v_a_4502_,
        v_a_4503_,
        v_a_4504_,
        v_a_4505_,
    );
    lean_dec(v_a_4505_);
    lean_dec_ref(v_a_4504_);
    lean_dec(v_a_4503_);
    lean_dec_ref(v_a_4502_);
    lean_dec_ref(v_mvarsNew_4498_);
    return v_res_4509_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(
    mut v_mvarId_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    v___x_4516_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(
        v_mvarId_4510_,
        v___y_4512_,
    );
    return v___x_4516_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(
    mut v_mvarId_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4523_: *mut LeanObject = core::ptr::null_mut();
    v_res_4523_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(
        v_mvarId_4517_,
        v___y_4518_,
        v___y_4519_,
        v___y_4520_,
        v___y_4521_,
    );
    lean_dec(v___y_4521_);
    lean_dec_ref(v___y_4520_);
    lean_dec(v___y_4519_);
    lean_dec_ref(v___y_4518_);
    lean_dec(v_mvarId_4517_);
    return v_res_4523_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(
    mut v_tacticName_4524_: *mut LeanObject,
    mut v_mvarId_4525_: *mut LeanObject,
    mut v_allowSynthFailures_4526_: u8,
    mut v_inst_4527_: *mut LeanObject,
    mut v_a_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
    mut v___y_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    v___x_4534_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_4524_, v_mvarId_4525_, v_allowSynthFailures_4526_, v_a_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
    return v___x_4534_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(
    mut v_tacticName_4535_: *mut LeanObject,
    mut v_mvarId_4536_: *mut LeanObject,
    mut v_allowSynthFailures_4537_: *mut LeanObject,
    mut v_inst_4538_: *mut LeanObject,
    mut v_a_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowSynthFailures_boxed_4545_: u8 = 0;
    let mut v_res_4546_: *mut LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4545_ = (lean_unbox(v_allowSynthFailures_4537_) as u8);
    v_res_4546_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(
            v_tacticName_4535_,
            v_mvarId_4536_,
            v_allowSynthFailures_boxed_4545_,
            v_inst_4538_,
            v_a_4539_,
            v___y_4540_,
            v___y_4541_,
            v___y_4542_,
            v___y_4543_,
        );
    lean_dec(v___y_4543_);
    lean_dec_ref(v___y_4542_);
    lean_dec(v___y_4541_);
    lean_dec_ref(v___y_4540_);
    return v_res_4546_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(
    mut v_00_u03b2_4547_: *mut LeanObject,
    mut v_x_4548_: *mut LeanObject,
    mut v_x_4549_: *mut LeanObject,
) -> u8 {
    let mut v___x_4550_: u8 = 0;
    v___x_4550_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_4548_, v_x_4549_);
    return v___x_4550_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(
    mut v_00_u03b2_4551_: *mut LeanObject,
    mut v_x_4552_: *mut LeanObject,
    mut v_x_4553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4554_: u8 = 0;
    let mut v_r_4555_: *mut LeanObject = core::ptr::null_mut();
    v_res_4554_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_4551_, v_x_4552_, v_x_4553_);
    lean_dec(v_x_4553_);
    lean_dec_ref(v_x_4552_);
    v_r_4555_ = lean_box((v_res_4554_) as usize);
    return v_r_4555_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4556_: *mut LeanObject,
    mut v_x_4557_: *mut LeanObject,
    mut v_x_4558_: usize,
    mut v_x_4559_: *mut LeanObject,
) -> u8 {
    let mut v___x_4560_: u8 = 0;
    v___x_4560_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_4557_, v_x_4558_, v_x_4559_);
    return v___x_4560_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4561_: *mut LeanObject,
    mut v_x_4562_: *mut LeanObject,
    mut v_x_4563_: *mut LeanObject,
    mut v_x_4564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3370__boxed_4565_: usize = 0;
    let mut v_res_4566_: u8 = 0;
    let mut v_r_4567_: *mut LeanObject = core::ptr::null_mut();
    v_x_3370__boxed_4565_ = lean_unbox_usize(v_x_4563_);
    lean_dec(v_x_4563_);
    v_res_4566_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_4561_, v_x_4562_, v_x_3370__boxed_4565_, v_x_4564_);
    lean_dec(v_x_4564_);
    lean_dec_ref(v_x_4562_);
    v_r_4567_ = lean_box((v_res_4566_) as usize);
    return v_r_4567_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4568_: *mut LeanObject,
    mut v_keys_4569_: *mut LeanObject,
    mut v_vals_4570_: *mut LeanObject,
    mut v_heq_4571_: *mut LeanObject,
    mut v_i_4572_: *mut LeanObject,
    mut v_k_4573_: *mut LeanObject,
) -> u8 {
    let mut v___x_4574_: u8 = 0;
    v___x_4574_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_4569_, v_i_4572_, v_k_4573_);
    return v___x_4574_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_4575_: *mut LeanObject,
    mut v_keys_4576_: *mut LeanObject,
    mut v_vals_4577_: *mut LeanObject,
    mut v_heq_4578_: *mut LeanObject,
    mut v_i_4579_: *mut LeanObject,
    mut v_k_4580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4581_: u8 = 0;
    let mut v_r_4582_: *mut LeanObject = core::ptr::null_mut();
    v_res_4581_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4575_, v_keys_4576_, v_vals_4577_, v_heq_4578_, v_i_4579_, v_k_4580_);
    lean_dec(v_k_4580_);
    lean_dec_ref(v_vals_4577_);
    lean_dec_ref(v_keys_4576_);
    v_r_4582_ = lean_box((v_res_4581_) as usize);
    return v_r_4582_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(
    mut v_newMVars_4583_: *mut LeanObject,
    mut v_binderInfos_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
    mut v_n_4586_: *mut LeanObject,
    mut v_i_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4594_: u8 = 0;
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: u8 = 0;
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: u8 = 0;
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4619_: u8 = 0;
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4593_ = lean_unsigned_to_nat(0);
                v_isZero_4594_ = lean_nat_dec_eq(v_i_4587_, v_zero_4593_);
                if v_isZero_4594_ == 1 {
                    lean_dec(v_i_4587_);
                    lean_dec(v_a_4585_);
                    v___x_4595_ = lean_box(0);
                    v___x_4596_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4596_, 0, v___x_4595_);
                    return v___x_4596_;
                } else {
                    v_one_4597_ = lean_unsigned_to_nat(1);
                    v_n_4598_ = lean_nat_sub(v_i_4587_, v_one_4597_);
                    lean_dec(v_i_4587_);
                    v___x_4599_ = lean_nat_sub(v_n_4586_, v_n_4598_);
                    v___x_4600_ = lean_nat_sub(v___x_4599_, v_one_4597_);
                    lean_dec(v___x_4599_);
                    v___x_4601_ = lean_array_fget_borrowed(v_newMVars_4583_, v___x_4600_);
                    v___x_4602_ = l_Lean_Expr_mvarId_x21(v___x_4601_);
                    v___x_4603_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_4602_, v___y_4589_);
                    v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
                    lean_inc(v_a_4604_);
                    lean_dec_ref(v___x_4603_);
                    v___x_4605_ = (lean_unbox(v_a_4604_) as u8);
                    lean_dec(v_a_4604_);
                    if v___x_4605_ == 0 {
                        v___x_4606_ = 0;
                        v___x_4607_ = lean_box((v___x_4606_) as usize);
                        v___x_4608_ = lean_array_get(v___x_4607_, v_binderInfos_4584_, v___x_4600_);
                        lean_dec(v___x_4600_);
                        lean_dec(v___x_4607_);
                        v___x_4609_ = (lean_unbox(v___x_4608_) as u8);
                        lean_dec(v___x_4608_);
                        v___x_4610_ = l_Lean_BinderInfo_isInstImplicit(v___x_4609_);
                        if v___x_4610_ == 0 {
                            lean_inc(v___x_4602_);
                            v___x_4611_ = l_Lean_MVarId_getTag(
                                v___x_4602_,
                                v___y_4588_,
                                v___y_4589_,
                                v___y_4590_,
                                v___y_4591_,
                            );
                            if lean_obj_tag(v___x_4611_) == 0 {
                                v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
                                lean_inc(v_a_4612_);
                                lean_dec_ref_known(v___x_4611_, 1);
                                lean_inc(v_a_4585_);
                                v___x_4613_ = l_Lean_Meta_appendTag(v_a_4585_, v_a_4612_);
                                v___x_4614_ = l_Lean_MVarId_setTag___redArg(
                                    v___x_4602_,
                                    v___x_4613_,
                                    v___y_4589_,
                                );
                                if lean_obj_tag(v___x_4614_) == 0 {
                                    lean_dec_ref_known(v___x_4614_, 1);
                                    v_i_4587_ = v_n_4598_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec(v_n_4598_);
                                    lean_dec(v_a_4585_);
                                    return v___x_4614_;
                                }
                            } else {
                                lean_dec(v___x_4602_);
                                lean_dec(v_n_4598_);
                                lean_dec(v_a_4585_);
                                v_a_4616_ = lean_ctor_get(v___x_4611_, 0);
                                v_isSharedCheck_4623_ = (!lean_is_exclusive(v___x_4611_)) as u8;
                                if v_isSharedCheck_4623_ == 0 {
                                    v___x_4618_ = v___x_4611_;
                                    v_isShared_4619_ = v_isSharedCheck_4623_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4616_);
                                    lean_dec(v___x_4611_);
                                    v___x_4618_ = lean_box(0);
                                    v_isShared_4619_ = v_isSharedCheck_4623_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4602_);
                            v_i_4587_ = v_n_4598_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4602_);
                        lean_dec(v___x_4600_);
                        v_i_4587_ = v_n_4598_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4619_ == 0 {
                    v___x_4621_ = v___x_4618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
                    v___x_4621_ = v_reuseFailAlloc_4622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(
    mut v_newMVars_4626_: *mut LeanObject,
    mut v_binderInfos_4627_: *mut LeanObject,
    mut v_a_4628_: *mut LeanObject,
    mut v_n_4629_: *mut LeanObject,
    mut v_i_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4636_: *mut LeanObject = core::ptr::null_mut();
    v_res_4636_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_4626_, v_binderInfos_4627_, v_a_4628_, v_n_4629_, v_i_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
    lean_dec(v___y_4634_);
    lean_dec_ref(v___y_4633_);
    lean_dec(v___y_4632_);
    lean_dec_ref(v___y_4631_);
    lean_dec(v_n_4629_);
    lean_dec_ref(v_binderInfos_4627_);
    lean_dec_ref(v_newMVars_4626_);
    return v_res_4636_;
}
pub unsafe fn l_Lean_Meta_appendParentTag(
    mut v_mvarId_4637_: *mut LeanObject,
    mut v_newMVars_4638_: *mut LeanObject,
    mut v_binderInfos_4639_: *mut LeanObject,
    mut v_a_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_a_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v_a_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4668_: u8 = 0;
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4645_ = l_Lean_MVarId_getTag(
                    v_mvarId_4637_,
                    v_a_4640_,
                    v_a_4641_,
                    v_a_4642_,
                    v_a_4643_,
                );
                if lean_obj_tag(v___x_4645_) == 0 {
                    v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
                    v_isSharedCheck_4664_ = (!lean_is_exclusive(v___x_4645_)) as u8;
                    if v_isSharedCheck_4664_ == 0 {
                        v___x_4648_ = v___x_4645_;
                        v_isShared_4649_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4646_);
                        lean_dec(v___x_4645_);
                        v___x_4648_ = lean_box(0);
                        v_isShared_4649_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4665_ = lean_ctor_get(v___x_4645_, 0);
                    v_isSharedCheck_4672_ = (!lean_is_exclusive(v___x_4645_)) as u8;
                    if v_isSharedCheck_4672_ == 0 {
                        v___x_4667_ = v___x_4645_;
                        v_isShared_4668_ = v_isSharedCheck_4672_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4665_);
                        lean_dec(v___x_4645_);
                        v___x_4667_ = lean_box(0);
                        v_isShared_4668_ = v_isSharedCheck_4672_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4650_ = lean_array_get_size(v_newMVars_4638_);
                v___x_4651_ = lean_unsigned_to_nat(1);
                v___x_4652_ = lean_nat_dec_eq(v___x_4650_, v___x_4651_);
                if v___x_4652_ == 0 {
                    v___x_4653_ = l_Lean_Name_isAnonymous(v_a_4646_);
                    if v___x_4653_ == 0 {
                        lean_del_object(v___x_4648_);
                        v___x_4654_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_4638_, v_binderInfos_4639_, v_a_4646_, v___x_4650_, v___x_4650_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
                        return v___x_4654_;
                    } else {
                        lean_dec(v_a_4646_);
                        v___x_4655_ = lean_box(0);
                        if v_isShared_4649_ == 0 {
                            lean_ctor_set(v___x_4648_, 0, v___x_4655_);
                            v___x_4657_ = v___x_4648_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
                            v___x_4657_ = v_reuseFailAlloc_4658_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4648_);
                    v___x_4659_ = l_Lean_instInhabitedExpr;
                    v___x_4660_ = lean_unsigned_to_nat(0);
                    v___x_4661_ =
                        lean_array_get_borrowed(v___x_4659_, v_newMVars_4638_, v___x_4660_);
                    v___x_4662_ = l_Lean_Expr_mvarId_x21(v___x_4661_);
                    v___x_4663_ = l_Lean_MVarId_setTag___redArg(v___x_4662_, v_a_4646_, v_a_4641_);
                    return v___x_4663_;
                }
            }
            2 => {
                return v___x_4657_;
            }
            3 => {
                if v_isShared_4668_ == 0 {
                    v___x_4670_ = v___x_4667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
                    v___x_4670_ = v_reuseFailAlloc_4671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_appendParentTag___boxed(
    mut v_mvarId_4673_: *mut LeanObject,
    mut v_newMVars_4674_: *mut LeanObject,
    mut v_binderInfos_4675_: *mut LeanObject,
    mut v_a_4676_: *mut LeanObject,
    mut v_a_4677_: *mut LeanObject,
    mut v_a_4678_: *mut LeanObject,
    mut v_a_4679_: *mut LeanObject,
    mut v_a_4680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4681_: *mut LeanObject = core::ptr::null_mut();
    v_res_4681_ = l_Lean_Meta_appendParentTag(
        v_mvarId_4673_,
        v_newMVars_4674_,
        v_binderInfos_4675_,
        v_a_4676_,
        v_a_4677_,
        v_a_4678_,
        v_a_4679_,
    );
    lean_dec(v_a_4679_);
    lean_dec_ref(v_a_4678_);
    lean_dec(v_a_4677_);
    lean_dec_ref(v_a_4676_);
    lean_dec_ref(v_binderInfos_4675_);
    lean_dec_ref(v_newMVars_4674_);
    return v_res_4681_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(
    mut v_newMVars_4682_: *mut LeanObject,
    mut v_binderInfos_4683_: *mut LeanObject,
    mut v_a_4684_: *mut LeanObject,
    mut v_n_4685_: *mut LeanObject,
    mut v_i_4686_: *mut LeanObject,
    mut v_a_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    v___x_4693_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_4682_, v_binderInfos_4683_, v_a_4684_, v_n_4685_, v_i_4686_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
    return v___x_4693_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(
    mut v_newMVars_4694_: *mut LeanObject,
    mut v_binderInfos_4695_: *mut LeanObject,
    mut v_a_4696_: *mut LeanObject,
    mut v_n_4697_: *mut LeanObject,
    mut v_i_4698_: *mut LeanObject,
    mut v_a_4699_: *mut LeanObject,
    mut v___y_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4705_: *mut LeanObject = core::ptr::null_mut();
    v_res_4705_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_4694_, v_binderInfos_4695_, v_a_4696_, v_n_4697_, v_i_4698_, v_a_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
    lean_dec(v___y_4703_);
    lean_dec_ref(v___y_4702_);
    lean_dec(v___y_4701_);
    lean_dec_ref(v___y_4700_);
    lean_dec(v_n_4697_);
    lean_dec_ref(v_binderInfos_4695_);
    lean_dec_ref(v_newMVars_4694_);
    return v_res_4705_;
}
pub unsafe fn l_Lean_Meta_postprocessAppMVars(
    mut v_tacticName_4706_: *mut LeanObject,
    mut v_mvarId_4707_: *mut LeanObject,
    mut v_newMVars_4708_: *mut LeanObject,
    mut v_binderInfos_4709_: *mut LeanObject,
    mut v_synthAssignedInstances_4710_: u8,
    mut v_allowSynthFailures_4711_: u8,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
    mut v_a_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    v___x_4717_ = l_Lean_Meta_synthAppInstances(
        v_tacticName_4706_,
        v_mvarId_4707_,
        v_newMVars_4708_,
        v_binderInfos_4709_,
        v_synthAssignedInstances_4710_,
        v_allowSynthFailures_4711_,
        v_a_4712_,
        v_a_4713_,
        v_a_4714_,
        v_a_4715_,
    );
    return v___x_4717_;
}
pub unsafe fn l_Lean_Meta_postprocessAppMVars___boxed(
    mut v_tacticName_4718_: *mut LeanObject,
    mut v_mvarId_4719_: *mut LeanObject,
    mut v_newMVars_4720_: *mut LeanObject,
    mut v_binderInfos_4721_: *mut LeanObject,
    mut v_synthAssignedInstances_4722_: *mut LeanObject,
    mut v_allowSynthFailures_4723_: *mut LeanObject,
    mut v_a_4724_: *mut LeanObject,
    mut v_a_4725_: *mut LeanObject,
    mut v_a_4726_: *mut LeanObject,
    mut v_a_4727_: *mut LeanObject,
    mut v_a_4728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthAssignedInstances_boxed_4729_: u8 = 0;
    let mut v_allowSynthFailures_boxed_4730_: u8 = 0;
    let mut v_res_4731_: *mut LeanObject = core::ptr::null_mut();
    v_synthAssignedInstances_boxed_4729_ = (lean_unbox(v_synthAssignedInstances_4722_) as u8);
    v_allowSynthFailures_boxed_4730_ = (lean_unbox(v_allowSynthFailures_4723_) as u8);
    v_res_4731_ = l_Lean_Meta_postprocessAppMVars(
        v_tacticName_4718_,
        v_mvarId_4719_,
        v_newMVars_4720_,
        v_binderInfos_4721_,
        v_synthAssignedInstances_boxed_4729_,
        v_allowSynthFailures_boxed_4730_,
        v_a_4724_,
        v_a_4725_,
        v_a_4726_,
        v_a_4727_,
    );
    lean_dec(v_a_4727_);
    lean_dec_ref(v_a_4726_);
    lean_dec(v_a_4725_);
    lean_dec_ref(v_a_4724_);
    lean_dec_ref(v_newMVars_4720_);
    return v_res_4731_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(
    mut v_mvar_4732_: *mut LeanObject,
    mut v_mvarId_4733_: *mut LeanObject,
) -> u8 {
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: u8 = 0;
    v___x_4734_ = l_Lean_Expr_mvarId_x21(v_mvar_4732_);
    v___x_4735_ = l_Lean_instBEqMVarId_beq(v_mvarId_4733_, v___x_4734_);
    lean_dec(v___x_4734_);
    return v___x_4735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(
    mut v_mvar_4736_: *mut LeanObject,
    mut v_mvarId_4737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4738_: u8 = 0;
    let mut v_r_4739_: *mut LeanObject = core::ptr::null_mut();
    v_res_4738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_4736_, v_mvarId_4737_);
    lean_dec(v_mvarId_4737_);
    lean_dec_ref(v_mvar_4736_);
    v_r_4739_ = lean_box((v_res_4738_) as usize);
    return v_r_4739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(
    mut v_mvar_4740_: *mut LeanObject,
    mut v_as_4741_: *mut LeanObject,
    mut v_i_4742_: usize,
    mut v_stop_4743_: usize,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4749_: u8 = 0;
    let mut v___x_4750_: u8 = 0;
    let mut v_a_4752_: u8 = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___f_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_a_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4776_: u8 = 0;
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4749_ = lean_usize_dec_eq(v_i_4742_, v_stop_4743_);
                if v___x_4749_ == 0 {
                    v___x_4750_ = 1;
                    v___x_4758_ = lean_array_uget_borrowed(v_as_4741_, v_i_4742_);
                    v___x_4759_ = lean_expr_eqv(v_mvar_4740_, v___x_4758_);
                    if v___x_4759_ == 0 {
                        lean_inc(v___y_4747_);
                        lean_inc_ref(v___y_4746_);
                        lean_inc(v___y_4745_);
                        lean_inc_ref(v___y_4744_);
                        lean_inc(v___x_4758_);
                        v___x_4760_ = lean_infer_type(
                            v___x_4758_,
                            v___y_4744_,
                            v___y_4745_,
                            v___y_4746_,
                            v___y_4747_,
                        );
                        if lean_obj_tag(v___x_4760_) == 0 {
                            v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
                            v_isSharedCheck_4772_ = (!lean_is_exclusive(v___x_4760_)) as u8;
                            if v_isSharedCheck_4772_ == 0 {
                                v___x_4763_ = v___x_4760_;
                                v_isShared_4764_ = v_isSharedCheck_4772_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_4761_);
                                lean_dec(v___x_4760_);
                                v___x_4763_ = lean_box(0);
                                v_isShared_4764_ = v_isSharedCheck_4772_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_mvar_4740_);
                            v_a_4773_ = lean_ctor_get(v___x_4760_, 0);
                            v_isSharedCheck_4780_ = (!lean_is_exclusive(v___x_4760_)) as u8;
                            if v_isSharedCheck_4780_ == 0 {
                                v___x_4775_ = v___x_4760_;
                                v_isShared_4776_ = v_isSharedCheck_4780_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4773_);
                                lean_dec(v___x_4760_);
                                v___x_4775_ = lean_box(0);
                                v_isShared_4776_ = v_isSharedCheck_4780_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_4752_ = v___x_4749_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mvar_4740_);
                    v___x_4781_ = 0;
                    v___x_4782_ = lean_box((v___x_4781_) as usize);
                    v___x_4783_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4783_, 0, v___x_4782_);
                    return v___x_4783_;
                }
            }
            1 => {
                if v_a_4752_ == 0 {
                    v___x_4753_ = 1usize;
                    v___x_4754_ = lean_usize_add(v_i_4742_, v___x_4753_);
                    v_i_4742_ = v___x_4754_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_mvar_4740_);
                    v___x_4756_ = lean_box((v___x_4750_) as usize);
                    v___x_4757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4757_, 0, v___x_4756_);
                    return v___x_4757_;
                }
            }
            2 => {
                lean_inc_ref(v_mvar_4740_);
                v___f_4765_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_4765_, 0, v_mvar_4740_);
                v___x_4766_ = lean_box(0);
                v___x_4767_ = l_Lean_FindMVar_main(v___f_4765_, v_a_4761_, v___x_4766_);
                if lean_obj_tag(v___x_4767_) == 0 {
                    lean_del_object(v___x_4763_);
                    v_a_4752_ = v___x_4759_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_4767_, 1);
                    lean_dec_ref(v_mvar_4740_);
                    v___x_4768_ = lean_box((v___x_4750_) as usize);
                    if v_isShared_4764_ == 0 {
                        lean_ctor_set(v___x_4763_, 0, v___x_4768_);
                        v___x_4770_ = v___x_4763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4768_);
                        v___x_4770_ = v_reuseFailAlloc_4771_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4770_;
            }
            4 => {
                if v_isShared_4776_ == 0 {
                    v___x_4778_ = v___x_4775_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
                    v___x_4778_ = v_reuseFailAlloc_4779_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(
    mut v_mvar_4784_: *mut LeanObject,
    mut v_as_4785_: *mut LeanObject,
    mut v_i_4786_: *mut LeanObject,
    mut v_stop_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4793_: usize = 0;
    let mut v_stop_boxed_4794_: usize = 0;
    let mut v_res_4795_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4793_ = lean_unbox_usize(v_i_4786_);
    lean_dec(v_i_4786_);
    v_stop_boxed_4794_ = lean_unbox_usize(v_stop_4787_);
    lean_dec(v_stop_4787_);
    v_res_4795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_4784_, v_as_4785_, v_i_boxed_4793_, v_stop_boxed_4794_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
    lean_dec(v___y_4791_);
    lean_dec_ref(v___y_4790_);
    lean_dec(v___y_4789_);
    lean_dec_ref(v___y_4788_);
    lean_dec_ref(v_as_4785_);
    return v_res_4795_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(
    mut v_mvar_4796_: *mut LeanObject,
    mut v_otherMVars_4797_: *mut LeanObject,
    mut v_a_4798_: *mut LeanObject,
    mut v_a_4799_: *mut LeanObject,
    mut v_a_4800_: *mut LeanObject,
    mut v_a_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: u8 = 0;
    v___x_4803_ = lean_unsigned_to_nat(0);
    v___x_4804_ = lean_array_get_size(v_otherMVars_4797_);
    v___x_4805_ = lean_nat_dec_lt(v___x_4803_, v___x_4804_);
    if v___x_4805_ == 0 {
        let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_mvar_4796_);
        v___x_4806_ = lean_box((v___x_4805_) as usize);
        v___x_4807_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4807_, 0, v___x_4806_);
        return v___x_4807_;
    } else {
        if v___x_4805_ == 0 {
            let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_mvar_4796_);
            v___x_4808_ = lean_box((v___x_4805_) as usize);
            v___x_4809_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_4809_, 0, v___x_4808_);
            return v___x_4809_;
        } else {
            let mut v___x_4810_: usize = 0;
            let mut v___x_4811_: usize = 0;
            let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
            v___x_4810_ = 0usize;
            v___x_4811_ = lean_usize_of_nat(v___x_4804_);
            v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_4796_, v_otherMVars_4797_, v___x_4810_, v___x_4811_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
            return v___x_4812_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(
    mut v_mvar_4813_: *mut LeanObject,
    mut v_otherMVars_4814_: *mut LeanObject,
    mut v_a_4815_: *mut LeanObject,
    mut v_a_4816_: *mut LeanObject,
    mut v_a_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
    mut v_a_4819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4820_: *mut LeanObject = core::ptr::null_mut();
    v_res_4820_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(
        v_mvar_4813_,
        v_otherMVars_4814_,
        v_a_4815_,
        v_a_4816_,
        v_a_4817_,
        v_a_4818_,
    );
    lean_dec(v_a_4818_);
    lean_dec_ref(v_a_4817_);
    lean_dec(v_a_4816_);
    lean_dec_ref(v_a_4815_);
    lean_dec_ref(v_otherMVars_4814_);
    return v_res_4820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(
    mut v_mvars_4821_: *mut LeanObject,
    mut v_as_4822_: *mut LeanObject,
    mut v_i_4823_: usize,
    mut v_stop_4824_: usize,
    mut v_b_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4831_: u8 = 0;
    let mut v_fst_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMVarId_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: usize = 0;
    let mut v___x_4844_: usize = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4831_ = lean_usize_dec_eq(v_i_4823_, v_stop_4824_);
                if v___x_4831_ == 0 {
                    v_fst_4832_ = lean_ctor_get(v_b_4825_, 0);
                    v_snd_4833_ = lean_ctor_get(v_b_4825_, 1);
                    v_isSharedCheck_4863_ = (!lean_is_exclusive(v_b_4825_)) as u8;
                    if v_isSharedCheck_4863_ == 0 {
                        v___x_4835_ = v_b_4825_;
                        v_isShared_4836_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4833_);
                        lean_inc(v_fst_4832_);
                        lean_dec(v_b_4825_);
                        v___x_4835_ = lean_box(0);
                        v_isShared_4836_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4864_, 0, v_b_4825_);
                    return v___x_4864_;
                }
            }
            1 => {
                v___x_4837_ = lean_array_uget_borrowed(v_as_4822_, v_i_4823_);
                v_currMVarId_4838_ = l_Lean_Expr_mvarId_x21(v___x_4837_);
                lean_inc(v___x_4837_);
                v___x_4839_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(
                    v___x_4837_,
                    v_mvars_4821_,
                    v___y_4826_,
                    v___y_4827_,
                    v___y_4828_,
                    v___y_4829_,
                );
                if lean_obj_tag(v___x_4839_) == 0 {
                    v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
                    lean_inc(v_a_4840_);
                    lean_dec_ref_known(v___x_4839_, 1);
                    v___x_4846_ = (lean_unbox(v_a_4840_) as u8);
                    lean_dec(v_a_4840_);
                    if v___x_4846_ == 0 {
                        v___x_4847_ = lean_array_push(v_fst_4832_, v_currMVarId_4838_);
                        if v_isShared_4836_ == 0 {
                            lean_ctor_set(v___x_4835_, 0, v___x_4847_);
                            v___x_4849_ = v___x_4835_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
                            lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_snd_4833_);
                            v___x_4849_ = v_reuseFailAlloc_4850_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4851_ = lean_array_push(v_snd_4833_, v_currMVarId_4838_);
                        if v_isShared_4836_ == 0 {
                            lean_ctor_set(v___x_4835_, 1, v___x_4851_);
                            v___x_4853_ = v___x_4835_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_fst_4832_);
                            lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___x_4851_);
                            v___x_4853_ = v_reuseFailAlloc_4854_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_currMVarId_4838_);
                    lean_del_object(v___x_4835_);
                    lean_dec(v_snd_4833_);
                    lean_dec(v_fst_4832_);
                    v_a_4855_ = lean_ctor_get(v___x_4839_, 0);
                    v_isSharedCheck_4862_ = (!lean_is_exclusive(v___x_4839_)) as u8;
                    if v_isSharedCheck_4862_ == 0 {
                        v___x_4857_ = v___x_4839_;
                        v_isShared_4858_ = v_isSharedCheck_4862_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4855_);
                        lean_dec(v___x_4839_);
                        v___x_4857_ = lean_box(0);
                        v_isShared_4858_ = v_isSharedCheck_4862_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4843_ = 1usize;
                v___x_4844_ = lean_usize_add(v_i_4823_, v___x_4843_);
                v_i_4823_ = v___x_4844_;
                v_b_4825_ = v_a_4842_;
                state = 0;
                continue;
            }
            3 => {
                v_a_4842_ = v___x_4849_;
                state = 2;
                continue;
            }
            4 => {
                v_a_4842_ = v___x_4853_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_4858_ == 0 {
                    v___x_4860_ = v___x_4857_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
                    v___x_4860_ = v_reuseFailAlloc_4861_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(
    mut v_mvars_4865_: *mut LeanObject,
    mut v_as_4866_: *mut LeanObject,
    mut v_i_4867_: *mut LeanObject,
    mut v_stop_4868_: *mut LeanObject,
    mut v_b_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4875_: usize = 0;
    let mut v_stop_boxed_4876_: usize = 0;
    let mut v_res_4877_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4875_ = lean_unbox_usize(v_i_4867_);
    lean_dec(v_i_4867_);
    v_stop_boxed_4876_ = lean_unbox_usize(v_stop_4868_);
    lean_dec(v_stop_4868_);
    v_res_4877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_4865_, v_as_4866_, v_i_boxed_4875_, v_stop_boxed_4876_, v_b_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
    lean_dec(v___y_4873_);
    lean_dec_ref(v___y_4872_);
    lean_dec(v___y_4871_);
    lean_dec_ref(v___y_4870_);
    lean_dec_ref(v_as_4866_);
    lean_dec_ref(v_mvars_4865_);
    return v_res_4877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
    mut v_mvars_4882_: *mut LeanObject,
    mut v_a_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    v___x_4888_ = lean_unsigned_to_nat(0);
    v___x_4889_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
    v___x_4890_ = lean_array_get_size(v_mvars_4882_);
    v___x_4891_ = lean_nat_dec_lt(v___x_4888_, v___x_4890_);
    if v___x_4891_ == 0 {
        let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
        v___x_4892_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4892_, 0, v___x_4889_);
        return v___x_4892_;
    } else {
        let mut v___x_4893_: u8 = 0;
        v___x_4893_ = lean_nat_dec_le(v___x_4890_, v___x_4890_);
        if v___x_4893_ == 0 {
            if v___x_4891_ == 0 {
                let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
                v___x_4894_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4894_, 0, v___x_4889_);
                return v___x_4894_;
            } else {
                let mut v___x_4895_: usize = 0;
                let mut v___x_4896_: usize = 0;
                let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
                v___x_4895_ = 0usize;
                v___x_4896_ = lean_usize_of_nat(v___x_4890_);
                v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_4882_, v_mvars_4882_, v___x_4895_, v___x_4896_, v___x_4889_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
                return v___x_4897_;
            }
        } else {
            let mut v___x_4898_: usize = 0;
            let mut v___x_4899_: usize = 0;
            let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
            v___x_4898_ = 0usize;
            v___x_4899_ = lean_usize_of_nat(v___x_4890_);
            v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_4882_, v_mvars_4882_, v___x_4898_, v___x_4899_, v___x_4889_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
            return v___x_4900_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(
    mut v_mvars_4901_: *mut LeanObject,
    mut v_a_4902_: *mut LeanObject,
    mut v_a_4903_: *mut LeanObject,
    mut v_a_4904_: *mut LeanObject,
    mut v_a_4905_: *mut LeanObject,
    mut v_a_4906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4907_: *mut LeanObject = core::ptr::null_mut();
    v_res_4907_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
        v_mvars_4901_,
        v_a_4902_,
        v_a_4903_,
        v_a_4904_,
        v_a_4905_,
    );
    lean_dec(v_a_4905_);
    lean_dec_ref(v_a_4904_);
    lean_dec(v_a_4903_);
    lean_dec_ref(v_a_4902_);
    lean_dec_ref(v_mvars_4901_);
    return v_res_4907_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(
    mut v_a_4908_: *mut LeanObject,
    mut v_a_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4908_) == 0 {
                    v___x_4910_ = l_List_reverse___redArg(v_a_4909_);
                    return v___x_4910_;
                } else {
                    v_head_4911_ = lean_ctor_get(v_a_4908_, 0);
                    v_tail_4912_ = lean_ctor_get(v_a_4908_, 1);
                    v_isSharedCheck_4921_ = (!lean_is_exclusive(v_a_4908_)) as u8;
                    if v_isSharedCheck_4921_ == 0 {
                        v___x_4914_ = v_a_4908_;
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4912_);
                        lean_inc(v_head_4911_);
                        lean_dec(v_a_4908_);
                        v___x_4914_ = lean_box(0);
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4916_ = l_Lean_Expr_mvarId_x21(v_head_4911_);
                lean_dec(v_head_4911_);
                if v_isShared_4915_ == 0 {
                    lean_ctor_set(v___x_4914_, 1, v_a_4909_);
                    lean_ctor_set(v___x_4914_, 0, v___x_4916_);
                    v___x_4918_ = v___x_4914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4916_);
                    lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_a_4909_);
                    v___x_4918_ = v_reuseFailAlloc_4920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4908_ = v_tail_4912_;
                v_a_4909_ = v___x_4918_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(
    mut v_mvars_4922_: *mut LeanObject,
    mut v_x_4923_: u8,
    mut v_a_4924_: *mut LeanObject,
    mut v_a_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v_fst_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4942_: u8 = 0;
    let mut v_a_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4950_: u8 = 0;
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v_fst_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_a_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4923_ {
                0 => {
                    v___x_4929_ =
                        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
                            v_mvars_4922_,
                            v_a_4924_,
                            v_a_4925_,
                            v_a_4926_,
                            v_a_4927_,
                        );
                    lean_dec_ref(v_mvars_4922_);
                    if lean_obj_tag(v___x_4929_) == 0 {
                        v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
                        v_isSharedCheck_4942_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                        if v_isSharedCheck_4942_ == 0 {
                            v___x_4932_ = v___x_4929_;
                            v_isShared_4933_ = v_isSharedCheck_4942_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4930_);
                            lean_dec(v___x_4929_);
                            v___x_4932_ = lean_box(0);
                            v_isShared_4933_ = v_isSharedCheck_4942_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4943_ = lean_ctor_get(v___x_4929_, 0);
                        v_isSharedCheck_4950_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                        if v_isSharedCheck_4950_ == 0 {
                            v___x_4945_ = v___x_4929_;
                            v_isShared_4946_ = v_isSharedCheck_4950_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4943_);
                            lean_dec(v___x_4929_);
                            v___x_4945_ = lean_box(0);
                            v_isShared_4946_ = v_isSharedCheck_4950_;
                            state = 3;
                            continue;
                        }
                    }
                }
                1 => {
                    v___x_4951_ =
                        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
                            v_mvars_4922_,
                            v_a_4924_,
                            v_a_4925_,
                            v_a_4926_,
                            v_a_4927_,
                        );
                    lean_dec_ref(v_mvars_4922_);
                    if lean_obj_tag(v___x_4951_) == 0 {
                        v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
                        v_isSharedCheck_4961_ = (!lean_is_exclusive(v___x_4951_)) as u8;
                        if v_isSharedCheck_4961_ == 0 {
                            v___x_4954_ = v___x_4951_;
                            v_isShared_4955_ = v_isSharedCheck_4961_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4952_);
                            lean_dec(v___x_4951_);
                            v___x_4954_ = lean_box(0);
                            v_isShared_4955_ = v_isSharedCheck_4961_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4962_ = lean_ctor_get(v___x_4951_, 0);
                        v_isSharedCheck_4969_ = (!lean_is_exclusive(v___x_4951_)) as u8;
                        if v_isSharedCheck_4969_ == 0 {
                            v___x_4964_ = v___x_4951_;
                            v_isShared_4965_ = v_isSharedCheck_4969_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4962_);
                            lean_dec(v___x_4951_);
                            v___x_4964_ = lean_box(0);
                            v_isShared_4965_ = v_isSharedCheck_4969_;
                            state = 7;
                            continue;
                        }
                    }
                }
                _ => {
                    v___x_4970_ = lean_array_to_list(v_mvars_4922_);
                    v___x_4971_ = lean_box(0);
                    v___x_4972_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_4970_, v___x_4971_);
                    v___x_4973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4973_, 0, v___x_4972_);
                    return v___x_4973_;
                }
            },
            1 => {
                v_fst_4934_ = lean_ctor_get(v_a_4930_, 0);
                lean_inc(v_fst_4934_);
                v_snd_4935_ = lean_ctor_get(v_a_4930_, 1);
                lean_inc(v_snd_4935_);
                lean_dec(v_a_4930_);
                v___x_4936_ = lean_array_to_list(v_fst_4934_);
                v___x_4937_ = lean_array_to_list(v_snd_4935_);
                v___x_4938_ = l_List_appendTR___redArg(v___x_4936_, v___x_4937_);
                if v_isShared_4933_ == 0 {
                    lean_ctor_set(v___x_4932_, 0, v___x_4938_);
                    v___x_4940_ = v___x_4932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
                    v___x_4940_ = v_reuseFailAlloc_4941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4940_;
            }
            3 => {
                if v_isShared_4946_ == 0 {
                    v___x_4948_ = v___x_4945_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
                    v___x_4948_ = v_reuseFailAlloc_4949_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4948_;
            }
            5 => {
                v_fst_4956_ = lean_ctor_get(v_a_4952_, 0);
                lean_inc(v_fst_4956_);
                lean_dec(v_a_4952_);
                v___x_4957_ = lean_array_to_list(v_fst_4956_);
                if v_isShared_4955_ == 0 {
                    lean_ctor_set(v___x_4954_, 0, v___x_4957_);
                    v___x_4959_ = v___x_4954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
                    v___x_4959_ = v_reuseFailAlloc_4960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4959_;
            }
            7 => {
                if v_isShared_4965_ == 0 {
                    v___x_4967_ = v___x_4964_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
                    v___x_4967_ = v_reuseFailAlloc_4968_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(
    mut v_mvars_4974_: *mut LeanObject,
    mut v_x_4975_: *mut LeanObject,
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_820__boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut LeanObject = core::ptr::null_mut();
    v_x_820__boxed_4981_ = (lean_unbox(v_x_4975_) as u8);
    v_res_4982_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(
        v_mvars_4974_,
        v_x_820__boxed_4981_,
        v_a_4976_,
        v_a_4977_,
        v_a_4978_,
        v_a_4979_,
    );
    lean_dec(v_a_4979_);
    lean_dec_ref(v_a_4978_);
    lean_dec(v_a_4977_);
    lean_dec_ref(v_a_4976_);
    return v_res_4982_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
    mut v_approx_4983_: u8,
    mut v_a_4984_: *mut LeanObject,
    mut v_b_4985_: *mut LeanObject,
    mut v_a_4986_: *mut LeanObject,
    mut v_a_4987_: *mut LeanObject,
    mut v_a_4988_: *mut LeanObject,
    mut v_a_4989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constApprox_4993_: u8 = 0;
    let mut v_isDefEqStuckEx_4994_: u8 = 0;
    let mut v_unificationHints_4995_: u8 = 0;
    let mut v_proofIrrelevance_4996_: u8 = 0;
    let mut v_assignSyntheticOpaque_4997_: u8 = 0;
    let mut v_offsetCnstrs_4998_: u8 = 0;
    let mut v_transparency_4999_: u8 = 0;
    let mut v_etaStruct_5000_: u8 = 0;
    let mut v_univApprox_5001_: u8 = 0;
    let mut v_iota_5002_: u8 = 0;
    let mut v_beta_5003_: u8 = 0;
    let mut v_proj_5004_: u8 = 0;
    let mut v_zeta_5005_: u8 = 0;
    let mut v_zetaDelta_5006_: u8 = 0;
    let mut v_zetaUnused_5007_: u8 = 0;
    let mut v_zetaHave_5008_: u8 = 0;
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5014_: u8 = 0;
    let mut v_zetaDeltaSet_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5021_: u8 = 0;
    let mut v_inTypeClassResolution_5022_: u8 = 0;
    let mut v_cacheInferType_5023_: u8 = 0;
    let mut v___x_5024_: u64 = 0;
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_approx_4983_ == 0 {
                    v___x_4991_ = l_Lean_Meta_isExprDefEqGuarded(
                        v_a_4984_, v_b_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_,
                    );
                    return v___x_4991_;
                } else {
                    v___x_4992_ = l_Lean_Meta_Context_config(v_a_4986_);
                    v_constApprox_4993_ = lean_ctor_get_uint8(v___x_4992_, 3 as u32);
                    v_isDefEqStuckEx_4994_ = lean_ctor_get_uint8(v___x_4992_, 4 as u32);
                    v_unificationHints_4995_ = lean_ctor_get_uint8(v___x_4992_, 5 as u32);
                    v_proofIrrelevance_4996_ = lean_ctor_get_uint8(v___x_4992_, 6 as u32);
                    v_assignSyntheticOpaque_4997_ = lean_ctor_get_uint8(v___x_4992_, 7 as u32);
                    v_offsetCnstrs_4998_ = lean_ctor_get_uint8(v___x_4992_, 8 as u32);
                    v_transparency_4999_ = lean_ctor_get_uint8(v___x_4992_, 9 as u32);
                    v_etaStruct_5000_ = lean_ctor_get_uint8(v___x_4992_, 10 as u32);
                    v_univApprox_5001_ = lean_ctor_get_uint8(v___x_4992_, 11 as u32);
                    v_iota_5002_ = lean_ctor_get_uint8(v___x_4992_, 12 as u32);
                    v_beta_5003_ = lean_ctor_get_uint8(v___x_4992_, 13 as u32);
                    v_proj_5004_ = lean_ctor_get_uint8(v___x_4992_, 14 as u32);
                    v_zeta_5005_ = lean_ctor_get_uint8(v___x_4992_, 15 as u32);
                    v_zetaDelta_5006_ = lean_ctor_get_uint8(v___x_4992_, 16 as u32);
                    v_zetaUnused_5007_ = lean_ctor_get_uint8(v___x_4992_, 17 as u32);
                    v_zetaHave_5008_ = lean_ctor_get_uint8(v___x_4992_, 18 as u32);
                    v_isSharedCheck_5029_ = (!lean_is_exclusive(v___x_4992_)) as u8;
                    if v_isSharedCheck_5029_ == 0 {
                        v___x_5010_ = v___x_4992_;
                        v_isShared_5011_ = v_isSharedCheck_5029_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4992_);
                        v___x_5010_ = lean_box(0);
                        v_isShared_5011_ = v_isSharedCheck_5029_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5011_ == 0 {
                    v___x_5013_ = v___x_5010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 3 as u32, v_constApprox_4993_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 4 as u32, v_isDefEqStuckEx_4994_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 5 as u32, v_unificationHints_4995_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 6 as u32, v_proofIrrelevance_4996_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        7 as u32,
                        v_assignSyntheticOpaque_4997_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 8 as u32, v_offsetCnstrs_4998_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 9 as u32, v_transparency_4999_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 10 as u32, v_etaStruct_5000_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 11 as u32, v_univApprox_5001_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 12 as u32, v_iota_5002_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 13 as u32, v_beta_5003_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 14 as u32, v_proj_5004_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 15 as u32, v_zeta_5005_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 16 as u32, v_zetaDelta_5006_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 17 as u32, v_zetaUnused_5007_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5028_, 18 as u32, v_zetaHave_5008_);
                    v___x_5013_ = v_reuseFailAlloc_5028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v___x_5013_, 0 as u32, v_approx_4983_);
                lean_ctor_set_uint8(v___x_5013_, 1 as u32, v_approx_4983_);
                lean_ctor_set_uint8(v___x_5013_, 2 as u32, v_approx_4983_);
                v_trackZetaDelta_5014_ = lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5015_ = lean_ctor_get(v_a_4986_, 1);
                v_lctx_5016_ = lean_ctor_get(v_a_4986_, 2);
                v_localInstances_5017_ = lean_ctor_get(v_a_4986_, 3);
                v_defEqCtx_x3f_5018_ = lean_ctor_get(v_a_4986_, 4);
                v_synthPendingDepth_5019_ = lean_ctor_get(v_a_4986_, 5);
                v_canUnfold_x3f_5020_ = lean_ctor_get(v_a_4986_, 6);
                v_univApprox_5021_ = lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5022_ = lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5023_ = lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_5024_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5013_);
                v___x_5025_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5025_, 0, v___x_5013_);
                lean_ctor_set_uint64(
                    v___x_5025_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5024_,
                );
                lean_inc(v_canUnfold_x3f_5020_);
                lean_inc(v_synthPendingDepth_5019_);
                lean_inc(v_defEqCtx_x3f_5018_);
                lean_inc_ref(v_localInstances_5017_);
                lean_inc_ref(v_lctx_5016_);
                lean_inc(v_zetaDeltaSet_5015_);
                v___x_5026_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5026_, 0, v___x_5025_);
                lean_ctor_set(v___x_5026_, 1, v_zetaDeltaSet_5015_);
                lean_ctor_set(v___x_5026_, 2, v_lctx_5016_);
                lean_ctor_set(v___x_5026_, 3, v_localInstances_5017_);
                lean_ctor_set(v___x_5026_, 4, v_defEqCtx_x3f_5018_);
                lean_ctor_set(v___x_5026_, 5, v_synthPendingDepth_5019_);
                lean_ctor_set(v___x_5026_, 6, v_canUnfold_x3f_5020_);
                lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5014_,
                );
                lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5021_,
                );
                lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5022_,
                );
                lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5023_,
                );
                v___x_5027_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_a_4984_,
                    v_b_4985_,
                    v___x_5026_,
                    v_a_4987_,
                    v_a_4988_,
                    v_a_4989_,
                );
                lean_dec_ref_known(v___x_5026_, 7);
                return v___x_5027_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(
    mut v_approx_5030_: *mut LeanObject,
    mut v_a_5031_: *mut LeanObject,
    mut v_b_5032_: *mut LeanObject,
    mut v_a_5033_: *mut LeanObject,
    mut v_a_5034_: *mut LeanObject,
    mut v_a_5035_: *mut LeanObject,
    mut v_a_5036_: *mut LeanObject,
    mut v_a_5037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_approx_boxed_5038_: u8 = 0;
    let mut v_res_5039_: *mut LeanObject = core::ptr::null_mut();
    v_approx_boxed_5038_ = (lean_unbox(v_approx_5030_) as u8);
    v_res_5039_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
        v_approx_boxed_5038_,
        v_a_5031_,
        v_b_5032_,
        v_a_5033_,
        v_a_5034_,
        v_a_5035_,
        v_a_5036_,
    );
    lean_dec(v_a_5036_);
    lean_dec_ref(v_a_5035_);
    lean_dec(v_a_5034_);
    lean_dec_ref(v_a_5033_);
    return v_res_5039_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(
    mut v_mvarId_5040_: *mut LeanObject,
    mut v_cfg_5041_: *mut LeanObject,
    mut v_term_x3f_5042_: *mut LeanObject,
    mut v_targetType_5043_: *mut LeanObject,
    mut v_eType_5044_: *mut LeanObject,
    mut v_rangeNumArgs_5045_: *mut LeanObject,
    mut v_i_5046_: *mut LeanObject,
    mut v_a_5047_: *mut LeanObject,
    mut v_a_5048_: *mut LeanObject,
    mut v_a_5049_: *mut LeanObject,
    mut v_a_5050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: u8 = 0;
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: u8 = 0;
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5068_: u8 = 0;
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5072_: u8 = 0;
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: u8 = 0;
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v_approx_5088_: u8 = 0;
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: u8 = 0;
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut v_a_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5117_: u8 = 0;
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5121_: u8 = 0;
    let mut v_isSharedCheck_5122_: u8 = 0;
    let mut v_a_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v_a_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5134_: u8 = 0;
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_5052_ = lean_ctor_get(v_rangeNumArgs_5045_, 0);
                v_upper_5053_ = lean_ctor_get(v_rangeNumArgs_5045_, 1);
                v___x_5054_ = lean_nat_dec_lt(v_i_5046_, v_upper_5053_);
                if v___x_5054_ == 0 {
                    lean_dec(v_i_5046_);
                    v___x_5055_ = lean_unsigned_to_nat(0);
                    v___x_5056_ = lean_nat_dec_eq(v_lower_5052_, v___x_5055_);
                    if v___x_5056_ == 0 {
                        lean_inc(v_lower_5052_);
                        v___x_5057_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5057_, 0, v_lower_5052_);
                        v___x_5058_ = 0;
                        lean_inc_ref(v_eType_5044_);
                        v___x_5059_ = l_Lean_Meta_forallMetaTelescopeReducing(
                            v_eType_5044_,
                            v___x_5057_,
                            v___x_5058_,
                            v_a_5047_,
                            v_a_5048_,
                            v_a_5049_,
                            v_a_5050_,
                        );
                        if lean_obj_tag(v___x_5059_) == 0 {
                            v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
                            lean_inc(v_a_5060_);
                            lean_dec_ref_known(v___x_5059_, 1);
                            v_snd_5061_ = lean_ctor_get(v_a_5060_, 1);
                            lean_inc(v_snd_5061_);
                            lean_dec(v_a_5060_);
                            v_snd_5062_ = lean_ctor_get(v_snd_5061_, 1);
                            lean_inc(v_snd_5062_);
                            lean_dec(v_snd_5061_);
                            v___x_5063_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5063_, 0, v_snd_5062_);
                            v___x_5064_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_5040_, v_eType_5044_, v___x_5063_, v_targetType_5043_, v_term_x3f_5042_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                            return v___x_5064_;
                        } else {
                            lean_dec_ref(v_eType_5044_);
                            lean_dec_ref(v_targetType_5043_);
                            lean_dec(v_term_x3f_5042_);
                            lean_dec(v_mvarId_5040_);
                            v_a_5065_ = lean_ctor_get(v___x_5059_, 0);
                            v_isSharedCheck_5072_ = (!lean_is_exclusive(v___x_5059_)) as u8;
                            if v_isSharedCheck_5072_ == 0 {
                                v___x_5067_ = v___x_5059_;
                                v_isShared_5068_ = v_isSharedCheck_5072_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5065_);
                                lean_dec(v___x_5059_);
                                v___x_5067_ = lean_box(0);
                                v_isShared_5068_ = v_isSharedCheck_5072_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_5073_ = lean_box(0);
                        v___x_5074_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_5040_, v_eType_5044_, v___x_5073_, v_targetType_5043_, v_term_x3f_5042_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                        return v___x_5074_;
                    }
                } else {
                    v___x_5075_ = l_Lean_Meta_saveState___redArg(v_a_5048_, v_a_5050_);
                    if lean_obj_tag(v___x_5075_) == 0 {
                        v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
                        lean_inc(v_a_5076_);
                        lean_dec_ref_known(v___x_5075_, 1);
                        lean_inc(v_i_5046_);
                        v___x_5077_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5077_, 0, v_i_5046_);
                        v___x_5078_ = 0;
                        lean_inc_ref(v_eType_5044_);
                        v___x_5079_ = l_Lean_Meta_forallMetaTelescopeReducing(
                            v_eType_5044_,
                            v___x_5077_,
                            v___x_5078_,
                            v_a_5047_,
                            v_a_5048_,
                            v_a_5049_,
                            v_a_5050_,
                        );
                        if lean_obj_tag(v___x_5079_) == 0 {
                            v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
                            lean_inc(v_a_5080_);
                            lean_dec_ref_known(v___x_5079_, 1);
                            v_snd_5081_ = lean_ctor_get(v_a_5080_, 1);
                            lean_inc(v_snd_5081_);
                            v_fst_5082_ = lean_ctor_get(v_a_5080_, 0);
                            lean_inc(v_fst_5082_);
                            lean_dec(v_a_5080_);
                            v_fst_5083_ = lean_ctor_get(v_snd_5081_, 0);
                            v_snd_5084_ = lean_ctor_get(v_snd_5081_, 1);
                            v_isSharedCheck_5122_ = (!lean_is_exclusive(v_snd_5081_)) as u8;
                            if v_isSharedCheck_5122_ == 0 {
                                v___x_5086_ = v_snd_5081_;
                                v_isShared_5087_ = v_isSharedCheck_5122_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_snd_5084_);
                                lean_inc(v_fst_5083_);
                                lean_dec(v_snd_5081_);
                                v___x_5086_ = lean_box(0);
                                v_isShared_5087_ = v_isSharedCheck_5122_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5076_);
                            lean_dec(v_i_5046_);
                            lean_dec_ref(v_eType_5044_);
                            lean_dec_ref(v_targetType_5043_);
                            lean_dec(v_term_x3f_5042_);
                            lean_dec(v_mvarId_5040_);
                            v_a_5123_ = lean_ctor_get(v___x_5079_, 0);
                            v_isSharedCheck_5130_ = (!lean_is_exclusive(v___x_5079_)) as u8;
                            if v_isSharedCheck_5130_ == 0 {
                                v___x_5125_ = v___x_5079_;
                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_5123_);
                                lean_dec(v___x_5079_);
                                v___x_5125_ = lean_box(0);
                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_i_5046_);
                        lean_dec_ref(v_eType_5044_);
                        lean_dec_ref(v_targetType_5043_);
                        lean_dec(v_term_x3f_5042_);
                        lean_dec(v_mvarId_5040_);
                        v_a_5131_ = lean_ctor_get(v___x_5075_, 0);
                        v_isSharedCheck_5138_ = (!lean_is_exclusive(v___x_5075_)) as u8;
                        if v_isSharedCheck_5138_ == 0 {
                            v___x_5133_ = v___x_5075_;
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5131_);
                            lean_dec(v___x_5075_);
                            v___x_5133_ = lean_box(0);
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5068_ == 0 {
                    v___x_5070_ = v___x_5067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
                    v___x_5070_ = v_reuseFailAlloc_5071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5070_;
            }
            3 => {
                v_approx_5088_ = lean_ctor_get_uint8(v_cfg_5041_, 3 as u32);
                lean_inc_ref(v_targetType_5043_);
                v___x_5089_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
                    v_approx_5088_,
                    v_snd_5084_,
                    v_targetType_5043_,
                    v_a_5047_,
                    v_a_5048_,
                    v_a_5049_,
                    v_a_5050_,
                );
                if lean_obj_tag(v___x_5089_) == 0 {
                    v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
                    v_isSharedCheck_5113_ = (!lean_is_exclusive(v___x_5089_)) as u8;
                    if v_isSharedCheck_5113_ == 0 {
                        v___x_5092_ = v___x_5089_;
                        v_isShared_5093_ = v_isSharedCheck_5113_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5090_);
                        lean_dec(v___x_5089_);
                        v___x_5092_ = lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5113_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5086_);
                    lean_dec(v_fst_5083_);
                    lean_dec(v_fst_5082_);
                    lean_dec(v_a_5076_);
                    lean_dec(v_i_5046_);
                    lean_dec_ref(v_eType_5044_);
                    lean_dec_ref(v_targetType_5043_);
                    lean_dec(v_term_x3f_5042_);
                    lean_dec(v_mvarId_5040_);
                    v_a_5114_ = lean_ctor_get(v___x_5089_, 0);
                    v_isSharedCheck_5121_ = (!lean_is_exclusive(v___x_5089_)) as u8;
                    if v_isSharedCheck_5121_ == 0 {
                        v___x_5116_ = v___x_5089_;
                        v_isShared_5117_ = v_isSharedCheck_5121_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5114_);
                        lean_dec(v___x_5089_);
                        v___x_5116_ = lean_box(0);
                        v_isShared_5117_ = v_isSharedCheck_5121_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5094_ = (lean_unbox(v_a_5090_) as u8);
                lean_dec(v_a_5090_);
                if v___x_5094_ == 0 {
                    lean_del_object(v___x_5092_);
                    lean_del_object(v___x_5086_);
                    lean_dec(v_fst_5083_);
                    lean_dec(v_fst_5082_);
                    v___x_5095_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_5076_, v_a_5048_, v_a_5050_);
                    lean_dec(v_a_5076_);
                    if lean_obj_tag(v___x_5095_) == 0 {
                        lean_dec_ref_known(v___x_5095_, 1);
                        v___x_5096_ = lean_unsigned_to_nat(1);
                        v___x_5097_ = lean_nat_add(v_i_5046_, v___x_5096_);
                        lean_dec(v_i_5046_);
                        v_i_5046_ = v___x_5097_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_5046_);
                        lean_dec_ref(v_eType_5044_);
                        lean_dec_ref(v_targetType_5043_);
                        lean_dec(v_term_x3f_5042_);
                        lean_dec(v_mvarId_5040_);
                        v_a_5099_ = lean_ctor_get(v___x_5095_, 0);
                        v_isSharedCheck_5106_ = (!lean_is_exclusive(v___x_5095_)) as u8;
                        if v_isSharedCheck_5106_ == 0 {
                            v___x_5101_ = v___x_5095_;
                            v_isShared_5102_ = v_isSharedCheck_5106_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5099_);
                            lean_dec(v___x_5095_);
                            v___x_5101_ = lean_box(0);
                            v_isShared_5102_ = v_isSharedCheck_5106_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5076_);
                    lean_dec(v_i_5046_);
                    lean_dec_ref(v_eType_5044_);
                    lean_dec_ref(v_targetType_5043_);
                    lean_dec(v_term_x3f_5042_);
                    lean_dec(v_mvarId_5040_);
                    if v_isShared_5087_ == 0 {
                        lean_ctor_set(v___x_5086_, 1, v_fst_5083_);
                        lean_ctor_set(v___x_5086_, 0, v_fst_5082_);
                        v___x_5108_ = v___x_5086_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_fst_5082_);
                        lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_fst_5083_);
                        v___x_5108_ = v_reuseFailAlloc_5112_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5102_ == 0 {
                    v___x_5104_ = v___x_5101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
                    v___x_5104_ = v_reuseFailAlloc_5105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5104_;
            }
            7 => {
                if v_isShared_5093_ == 0 {
                    lean_ctor_set(v___x_5092_, 0, v___x_5108_);
                    v___x_5110_ = v___x_5092_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
                    v___x_5110_ = v_reuseFailAlloc_5111_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5110_;
            }
            9 => {
                if v_isShared_5117_ == 0 {
                    v___x_5119_ = v___x_5116_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
                    v___x_5119_ = v_reuseFailAlloc_5120_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5119_;
            }
            11 => {
                if v_isShared_5126_ == 0 {
                    v___x_5128_ = v___x_5125_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
                    v___x_5128_ = v_reuseFailAlloc_5129_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5128_;
            }
            13 => {
                if v_isShared_5134_ == 0 {
                    v___x_5136_ = v___x_5133_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
                    v___x_5136_ = v_reuseFailAlloc_5137_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(
    mut v_mvarId_5139_: *mut LeanObject,
    mut v_cfg_5140_: *mut LeanObject,
    mut v_term_x3f_5141_: *mut LeanObject,
    mut v_targetType_5142_: *mut LeanObject,
    mut v_eType_5143_: *mut LeanObject,
    mut v_rangeNumArgs_5144_: *mut LeanObject,
    mut v_i_5145_: *mut LeanObject,
    mut v_a_5146_: *mut LeanObject,
    mut v_a_5147_: *mut LeanObject,
    mut v_a_5148_: *mut LeanObject,
    mut v_a_5149_: *mut LeanObject,
    mut v_a_5150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5151_: *mut LeanObject = core::ptr::null_mut();
    v_res_5151_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(
        v_mvarId_5139_,
        v_cfg_5140_,
        v_term_x3f_5141_,
        v_targetType_5142_,
        v_eType_5143_,
        v_rangeNumArgs_5144_,
        v_i_5145_,
        v_a_5146_,
        v_a_5147_,
        v_a_5148_,
        v_a_5149_,
    );
    lean_dec(v_a_5149_);
    lean_dec_ref(v_a_5148_);
    lean_dec(v_a_5147_);
    lean_dec_ref(v_a_5146_);
    lean_dec_ref(v_rangeNumArgs_5144_);
    lean_dec_ref(v_cfg_5140_);
    return v_res_5151_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(
    mut v_x_5152_: *mut LeanObject,
    mut v_h__1_5153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    v_snd_5154_ = lean_ctor_get(v_x_5152_, 1);
    lean_inc(v_snd_5154_);
    v_fst_5155_ = lean_ctor_get(v_x_5152_, 0);
    lean_inc(v_fst_5155_);
    lean_dec_ref(v_x_5152_);
    v_fst_5156_ = lean_ctor_get(v_snd_5154_, 0);
    lean_inc(v_fst_5156_);
    v_snd_5157_ = lean_ctor_get(v_snd_5154_, 1);
    lean_inc(v_snd_5157_);
    lean_dec(v_snd_5154_);
    v___x_5158_ = lean_apply_3(v_h__1_5153_, v_fst_5155_, v_fst_5156_, v_snd_5157_);
    return v___x_5158_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(
    mut v_motive_5159_: *mut LeanObject,
    mut v_x_5160_: *mut LeanObject,
    mut v_h__1_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    v_snd_5162_ = lean_ctor_get(v_x_5160_, 1);
    lean_inc(v_snd_5162_);
    v_fst_5163_ = lean_ctor_get(v_x_5160_, 0);
    lean_inc(v_fst_5163_);
    lean_dec_ref(v_x_5160_);
    v_fst_5164_ = lean_ctor_get(v_snd_5162_, 0);
    lean_inc(v_fst_5164_);
    v_snd_5165_ = lean_ctor_get(v_snd_5162_, 1);
    lean_inc(v_snd_5165_);
    lean_dec(v_snd_5162_);
    v___x_5166_ = lean_apply_3(v_h__1_5161_, v_fst_5163_, v_fst_5164_, v_snd_5165_);
    return v___x_5166_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(
    mut v_e_5167_: *mut LeanObject,
    mut v___y_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5170_: u8 = 0;
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_unused_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5170_ = l_Lean_Expr_hasMVar(v_e_5167_);
                if v___x_5170_ == 0 {
                    v___x_5171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5171_, 0, v_e_5167_);
                    return v___x_5171_;
                } else {
                    v___x_5172_ = lean_st_ref_get(v___y_5168_);
                    v_mctx_5173_ = lean_ctor_get(v___x_5172_, 0);
                    lean_inc_ref(v_mctx_5173_);
                    lean_dec(v___x_5172_);
                    v___x_5174_ = l_Lean_instantiateMVarsCore(v_mctx_5173_, v_e_5167_);
                    v_fst_5175_ = lean_ctor_get(v___x_5174_, 0);
                    lean_inc(v_fst_5175_);
                    v_snd_5176_ = lean_ctor_get(v___x_5174_, 1);
                    lean_inc(v_snd_5176_);
                    lean_dec_ref(v___x_5174_);
                    v___x_5177_ = lean_st_ref_take(v___y_5168_);
                    v_cache_5178_ = lean_ctor_get(v___x_5177_, 1);
                    v_zetaDeltaFVarIds_5179_ = lean_ctor_get(v___x_5177_, 2);
                    v_postponed_5180_ = lean_ctor_get(v___x_5177_, 3);
                    v_diag_5181_ = lean_ctor_get(v___x_5177_, 4);
                    v_isSharedCheck_5190_ = (!lean_is_exclusive(v___x_5177_)) as u8;
                    if v_isSharedCheck_5190_ == 0 {
                        v_unused_5191_ = lean_ctor_get(v___x_5177_, 0);
                        lean_dec(v_unused_5191_);
                        v___x_5183_ = v___x_5177_;
                        v_isShared_5184_ = v_isSharedCheck_5190_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5181_);
                        lean_inc(v_postponed_5180_);
                        lean_inc(v_zetaDeltaFVarIds_5179_);
                        lean_inc(v_cache_5178_);
                        lean_dec(v___x_5177_);
                        v___x_5183_ = lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5190_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5184_ == 0 {
                    lean_ctor_set(v___x_5183_, 0, v_snd_5176_);
                    v___x_5186_ = v___x_5183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_snd_5176_);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 1, v_cache_5178_);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 2, v_zetaDeltaFVarIds_5179_);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 3, v_postponed_5180_);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 4, v_diag_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5189_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5187_ = lean_st_ref_set(v___y_5168_, v___x_5186_);
                v___x_5188_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5188_, 0, v_fst_5175_);
                return v___x_5188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(
    mut v_e_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5195_: *mut LeanObject = core::ptr::null_mut();
    v_res_5195_ =
        l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_5192_, v___y_5193_);
    lean_dec(v___y_5193_);
    return v_res_5195_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(
    mut v_e_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    v___x_5202_ =
        l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_5196_, v___y_5198_);
    return v___x_5202_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(
    mut v_e_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5209_: *mut LeanObject = core::ptr::null_mut();
    v_res_5209_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(
        v_e_5203_,
        v___y_5204_,
        v___y_5205_,
        v___y_5206_,
        v___y_5207_,
    );
    lean_dec(v___y_5207_);
    lean_dec_ref(v___y_5206_);
    lean_dec(v___y_5205_);
    lean_dec_ref(v___y_5204_);
    return v_res_5209_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
    mut v_mvarId_5210_: *mut LeanObject,
    mut v_x_5211_: *mut LeanObject,
    mut v___y_5212_: *mut LeanObject,
    mut v___y_5213_: *mut LeanObject,
    mut v___y_5214_: *mut LeanObject,
    mut v___y_5215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5221_: u8 = 0;
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut v_a_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5217_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5210_,
                    v_x_5211_,
                    v___y_5212_,
                    v___y_5213_,
                    v___y_5214_,
                    v___y_5215_,
                );
                if lean_obj_tag(v___x_5217_) == 0 {
                    v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
                    v_isSharedCheck_5225_ = (!lean_is_exclusive(v___x_5217_)) as u8;
                    if v_isSharedCheck_5225_ == 0 {
                        v___x_5220_ = v___x_5217_;
                        v_isShared_5221_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5218_);
                        lean_dec(v___x_5217_);
                        v___x_5220_ = lean_box(0);
                        v_isShared_5221_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5226_ = lean_ctor_get(v___x_5217_, 0);
                    v_isSharedCheck_5233_ = (!lean_is_exclusive(v___x_5217_)) as u8;
                    if v_isSharedCheck_5233_ == 0 {
                        v___x_5228_ = v___x_5217_;
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5226_);
                        lean_dec(v___x_5217_);
                        v___x_5228_ = lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5221_ == 0 {
                    v___x_5223_ = v___x_5220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
                    v___x_5223_ = v_reuseFailAlloc_5224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5223_;
            }
            3 => {
                if v_isShared_5229_ == 0 {
                    v___x_5231_ = v___x_5228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(
    mut v_mvarId_5234_: *mut LeanObject,
    mut v_x_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5241_: *mut LeanObject = core::ptr::null_mut();
    v_res_5241_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_5234_,
        v_x_5235_,
        v___y_5236_,
        v___y_5237_,
        v___y_5238_,
        v___y_5239_,
    );
    lean_dec(v___y_5239_);
    lean_dec_ref(v___y_5238_);
    lean_dec(v___y_5237_);
    lean_dec_ref(v___y_5236_);
    return v_res_5241_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(
    mut v_00_u03b1_5242_: *mut LeanObject,
    mut v_mvarId_5243_: *mut LeanObject,
    mut v_x_5244_: *mut LeanObject,
    mut v___y_5245_: *mut LeanObject,
    mut v___y_5246_: *mut LeanObject,
    mut v___y_5247_: *mut LeanObject,
    mut v___y_5248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    v___x_5250_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_5243_,
        v_x_5244_,
        v___y_5245_,
        v___y_5246_,
        v___y_5247_,
        v___y_5248_,
    );
    return v___x_5250_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(
    mut v_00_u03b1_5251_: *mut LeanObject,
    mut v_mvarId_5252_: *mut LeanObject,
    mut v_x_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
    mut v___y_5258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5259_: *mut LeanObject = core::ptr::null_mut();
    v_res_5259_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(
        v_00_u03b1_5251_,
        v_mvarId_5252_,
        v_x_5253_,
        v___y_5254_,
        v___y_5255_,
        v___y_5256_,
        v___y_5257_,
    );
    lean_dec(v___y_5257_);
    lean_dec_ref(v___y_5256_);
    lean_dec(v___y_5255_);
    lean_dec_ref(v___y_5254_);
    return v_res_5259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(
    mut v_as_5260_: *mut LeanObject,
    mut v_i_5261_: usize,
    mut v_stop_5262_: usize,
    mut v_b_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: usize = 0;
    let mut v___x_5269_: usize = 0;
    let mut v___x_5271_: u8 = 0;
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v_a_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: u8 = 0;
    let mut v_a_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5284_: u8 = 0;
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5271_ = lean_usize_dec_eq(v_i_5261_, v_stop_5262_);
                if v___x_5271_ == 0 {
                    v___x_5272_ = lean_array_uget_borrowed(v_as_5260_, v_i_5261_);
                    v___x_5275_ = l_Lean_Expr_mvarId_x21(v___x_5272_);
                    v___x_5276_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_5275_, v___y_5264_);
                    lean_dec(v___x_5275_);
                    if lean_obj_tag(v___x_5276_) == 0 {
                        v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
                        lean_inc(v_a_5277_);
                        lean_dec_ref_known(v___x_5276_, 1);
                        v___x_5278_ = (lean_unbox(v_a_5277_) as u8);
                        lean_dec(v_a_5277_);
                        if v___x_5278_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_5267_ = v_b_5263_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_5276_) == 0 {
                            v_a_5279_ = lean_ctor_get(v___x_5276_, 0);
                            lean_inc(v_a_5279_);
                            lean_dec_ref_known(v___x_5276_, 1);
                            v___x_5280_ = (lean_unbox(v_a_5279_) as u8);
                            lean_dec(v_a_5279_);
                            if v___x_5280_ == 0 {
                                v_a_5267_ = v_b_5263_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_5263_);
                            v_a_5281_ = lean_ctor_get(v___x_5276_, 0);
                            v_isSharedCheck_5288_ = (!lean_is_exclusive(v___x_5276_)) as u8;
                            if v_isSharedCheck_5288_ == 0 {
                                v___x_5283_ = v___x_5276_;
                                v_isShared_5284_ = v_isSharedCheck_5288_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5281_);
                                lean_dec(v___x_5276_);
                                v___x_5283_ = lean_box(0);
                                v_isShared_5284_ = v_isSharedCheck_5288_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5289_, 0, v_b_5263_);
                    return v___x_5289_;
                }
            }
            1 => {
                v___x_5268_ = 1usize;
                v___x_5269_ = lean_usize_add(v_i_5261_, v___x_5268_);
                v_i_5261_ = v___x_5269_;
                v_b_5263_ = v_a_5267_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v___x_5272_);
                v___x_5274_ = lean_array_push(v_b_5263_, v___x_5272_);
                v_a_5267_ = v___x_5274_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_5284_ == 0 {
                    v___x_5286_ = v___x_5283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
                    v___x_5286_ = v_reuseFailAlloc_5287_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(
    mut v_as_5290_: *mut LeanObject,
    mut v_i_5291_: *mut LeanObject,
    mut v_stop_5292_: *mut LeanObject,
    mut v_b_5293_: *mut LeanObject,
    mut v___y_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5296_: usize = 0;
    let mut v_stop_boxed_5297_: usize = 0;
    let mut v_res_5298_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5296_ = lean_unbox_usize(v_i_5291_);
    lean_dec(v_i_5291_);
    v_stop_boxed_5297_ = lean_unbox_usize(v_stop_5292_);
    lean_dec(v_stop_5292_);
    v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_5290_, v_i_boxed_5296_, v_stop_boxed_5297_, v_b_5293_, v___y_5294_);
    lean_dec(v___y_5294_);
    lean_dec_ref(v_as_5290_);
    return v_res_5298_;
}
pub unsafe fn l_List_forM___at___00Lean_MVarId_apply_spec__3(
    mut v_as_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
    mut v___y_5301_: *mut LeanObject,
    mut v___y_5302_: *mut LeanObject,
    mut v___y_5303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_5299_) == 0 {
                    v___x_5305_ = lean_box(0);
                    v___x_5306_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5306_, 0, v___x_5305_);
                    return v___x_5306_;
                } else {
                    v_head_5307_ = lean_ctor_get(v_as_5299_, 0);
                    lean_inc(v_head_5307_);
                    v_tail_5308_ = lean_ctor_get(v_as_5299_, 1);
                    lean_inc(v_tail_5308_);
                    lean_dec_ref_known(v_as_5299_, 2);
                    v___x_5309_ = l_Lean_MVarId_headBetaType(
                        v_head_5307_,
                        v___y_5300_,
                        v___y_5301_,
                        v___y_5302_,
                        v___y_5303_,
                    );
                    if lean_obj_tag(v___x_5309_) == 0 {
                        lean_dec_ref_known(v___x_5309_, 1);
                        v_as_5299_ = v_tail_5308_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_5308_);
                        return v___x_5309_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(
    mut v_as_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
    mut v___y_5316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5317_: *mut LeanObject = core::ptr::null_mut();
    v_res_5317_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(
        v_as_5311_,
        v___y_5312_,
        v___y_5313_,
        v___y_5314_,
        v___y_5315_,
    );
    lean_dec(v___y_5315_);
    lean_dec_ref(v___y_5314_);
    lean_dec(v___y_5313_);
    lean_dec_ref(v___y_5312_);
    return v_res_5317_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(
    mut v_x_5318_: *mut LeanObject,
    mut v_x_5319_: *mut LeanObject,
    mut v_x_5320_: *mut LeanObject,
    mut v_x_5321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: u8 = 0;
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5322_ = lean_ctor_get(v_x_5318_, 0);
                v_vs_5323_ = lean_ctor_get(v_x_5318_, 1);
                v_isSharedCheck_5347_ = (!lean_is_exclusive(v_x_5318_)) as u8;
                if v_isSharedCheck_5347_ == 0 {
                    v___x_5325_ = v_x_5318_;
                    v_isShared_5326_ = v_isSharedCheck_5347_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_5323_);
                    lean_inc(v_ks_5322_);
                    lean_dec(v_x_5318_);
                    v___x_5325_ = lean_box(0);
                    v_isShared_5326_ = v_isSharedCheck_5347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5327_ = lean_array_get_size(v_ks_5322_);
                v___x_5328_ = lean_nat_dec_lt(v_x_5319_, v___x_5327_);
                if v___x_5328_ == 0 {
                    lean_dec(v_x_5319_);
                    v___x_5329_ = lean_array_push(v_ks_5322_, v_x_5320_);
                    v___x_5330_ = lean_array_push(v_vs_5323_, v_x_5321_);
                    if v_isShared_5326_ == 0 {
                        lean_ctor_set(v___x_5325_, 1, v___x_5330_);
                        lean_ctor_set(v___x_5325_, 0, v___x_5329_);
                        v___x_5332_ = v___x_5325_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5329_);
                        lean_ctor_set(v_reuseFailAlloc_5333_, 1, v___x_5330_);
                        v___x_5332_ = v_reuseFailAlloc_5333_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5334_ = lean_array_fget_borrowed(v_ks_5322_, v_x_5319_);
                    v___x_5335_ = l_Lean_instBEqMVarId_beq(v_x_5320_, v_k_x27_5334_);
                    if v___x_5335_ == 0 {
                        if v_isShared_5326_ == 0 {
                            v___x_5337_ = v___x_5325_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_ks_5322_);
                            lean_ctor_set(v_reuseFailAlloc_5341_, 1, v_vs_5323_);
                            v___x_5337_ = v_reuseFailAlloc_5341_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5342_ = lean_array_fset(v_ks_5322_, v_x_5319_, v_x_5320_);
                        v___x_5343_ = lean_array_fset(v_vs_5323_, v_x_5319_, v_x_5321_);
                        lean_dec(v_x_5319_);
                        if v_isShared_5326_ == 0 {
                            lean_ctor_set(v___x_5325_, 1, v___x_5343_);
                            lean_ctor_set(v___x_5325_, 0, v___x_5342_);
                            v___x_5345_ = v___x_5325_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5342_);
                            lean_ctor_set(v_reuseFailAlloc_5346_, 1, v___x_5343_);
                            v___x_5345_ = v_reuseFailAlloc_5346_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5332_;
            }
            3 => {
                v___x_5338_ = lean_unsigned_to_nat(1);
                v___x_5339_ = lean_nat_add(v_x_5319_, v___x_5338_);
                lean_dec(v_x_5319_);
                v_x_5318_ = v___x_5337_;
                v_x_5319_ = v___x_5339_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(
    mut v_n_5348_: *mut LeanObject,
    mut v_k_5349_: *mut LeanObject,
    mut v_v_5350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    v___x_5351_ = lean_unsigned_to_nat(0);
    v___x_5352_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_5348_, v___x_5351_, v_k_5349_, v_v_5350_);
    return v___x_5352_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    v___x_5353_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_5353_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(
    mut v_x_5354_: *mut LeanObject,
    mut v_x_5355_: usize,
    mut v_x_5356_: usize,
    mut v_x_5357_: *mut LeanObject,
    mut v_x_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5362_: usize = 0;
    let mut v___x_5363_: usize = 0;
    let mut v_j_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v_v_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5390_: u8 = 0;
    let mut v_node_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5395_: usize = 0;
    let mut v___x_5396_: usize = 0;
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5401_: u8 = 0;
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v_unused_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: u8 = 0;
    let mut v_ks_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: usize = 0;
    let mut v___x_5421_: u8 = 0;
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: u8 = 0;
    let mut v_reuseFailAlloc_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5354_) == 0 {
                    v_es_5359_ = lean_ctor_get(v_x_5354_, 0);
                    v___x_5360_ = 5usize;
                    v___x_5361_ = 1usize;
                    v___x_5362_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_5363_ = lean_usize_land(v_x_5355_, v___x_5362_);
                    v_j_5364_ = lean_usize_to_nat(v___x_5363_);
                    v___x_5365_ = lean_array_get_size(v_es_5359_);
                    v___x_5366_ = lean_nat_dec_lt(v_j_5364_, v___x_5365_);
                    if v___x_5366_ == 0 {
                        lean_dec(v_j_5364_);
                        lean_dec(v_x_5358_);
                        lean_dec(v_x_5357_);
                        return v_x_5354_;
                    } else {
                        lean_inc_ref(v_es_5359_);
                        v_isSharedCheck_5403_ = (!lean_is_exclusive(v_x_5354_)) as u8;
                        if v_isSharedCheck_5403_ == 0 {
                            v_unused_5404_ = lean_ctor_get(v_x_5354_, 0);
                            lean_dec(v_unused_5404_);
                            v___x_5368_ = v_x_5354_;
                            v_isShared_5369_ = v_isSharedCheck_5403_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_5354_);
                            v___x_5368_ = lean_box(0);
                            v_isShared_5369_ = v_isSharedCheck_5403_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5405_ = lean_ctor_get(v_x_5354_, 0);
                    v_vs_5406_ = lean_ctor_get(v_x_5354_, 1);
                    v_isSharedCheck_5426_ = (!lean_is_exclusive(v_x_5354_)) as u8;
                    if v_isSharedCheck_5426_ == 0 {
                        v___x_5408_ = v_x_5354_;
                        v_isShared_5409_ = v_isSharedCheck_5426_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_5406_);
                        lean_inc(v_ks_5405_);
                        lean_dec(v_x_5354_);
                        v___x_5408_ = lean_box(0);
                        v_isShared_5409_ = v_isSharedCheck_5426_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5370_ = lean_array_fget(v_es_5359_, v_j_5364_);
                v___x_5371_ = lean_box(0);
                v_xs_x27_5372_ = lean_array_fset(v_es_5359_, v_j_5364_, v___x_5371_);
                match lean_obj_tag(v_v_5370_) {
                    0 => {
                        v_key_5379_ = lean_ctor_get(v_v_5370_, 0);
                        v_val_5380_ = lean_ctor_get(v_v_5370_, 1);
                        v_isSharedCheck_5390_ = (!lean_is_exclusive(v_v_5370_)) as u8;
                        if v_isSharedCheck_5390_ == 0 {
                            v___x_5382_ = v_v_5370_;
                            v_isShared_5383_ = v_isSharedCheck_5390_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_5380_);
                            lean_inc(v_key_5379_);
                            lean_dec(v_v_5370_);
                            v___x_5382_ = lean_box(0);
                            v_isShared_5383_ = v_isSharedCheck_5390_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5391_ = lean_ctor_get(v_v_5370_, 0);
                        v_isSharedCheck_5401_ = (!lean_is_exclusive(v_v_5370_)) as u8;
                        if v_isSharedCheck_5401_ == 0 {
                            v___x_5393_ = v_v_5370_;
                            v_isShared_5394_ = v_isSharedCheck_5401_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_5391_);
                            lean_dec(v_v_5370_);
                            v___x_5393_ = lean_box(0);
                            v_isShared_5394_ = v_isSharedCheck_5401_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5402_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5402_, 0, v_x_5357_);
                        lean_ctor_set(v___x_5402_, 1, v_x_5358_);
                        v___y_5374_ = v___x_5402_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5375_ = lean_array_fset(v_xs_x27_5372_, v_j_5364_, v___y_5374_);
                lean_dec(v_j_5364_);
                if v_isShared_5369_ == 0 {
                    lean_ctor_set(v___x_5368_, 0, v___x_5375_);
                    v___x_5377_ = v___x_5368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
                    v___x_5377_ = v_reuseFailAlloc_5378_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5377_;
            }
            4 => {
                v___x_5384_ = l_Lean_instBEqMVarId_beq(v_x_5357_, v_key_5379_);
                if v___x_5384_ == 0 {
                    lean_del_object(v___x_5382_);
                    v___x_5385_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5379_,
                        v_val_5380_,
                        v_x_5357_,
                        v_x_5358_,
                    );
                    v___x_5386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5386_, 0, v___x_5385_);
                    v___y_5374_ = v___x_5386_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_5380_);
                    lean_dec(v_key_5379_);
                    if v_isShared_5383_ == 0 {
                        lean_ctor_set(v___x_5382_, 1, v_x_5358_);
                        lean_ctor_set(v___x_5382_, 0, v_x_5357_);
                        v___x_5388_ = v___x_5382_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_x_5357_);
                        lean_ctor_set(v_reuseFailAlloc_5389_, 1, v_x_5358_);
                        v___x_5388_ = v_reuseFailAlloc_5389_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5374_ = v___x_5388_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5395_ = lean_usize_shift_right(v_x_5355_, v___x_5360_);
                v___x_5396_ = lean_usize_add(v_x_5356_, v___x_5361_);
                v___x_5397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_5391_, v___x_5395_, v___x_5396_, v_x_5357_, v_x_5358_);
                if v_isShared_5394_ == 0 {
                    lean_ctor_set(v___x_5393_, 0, v___x_5397_);
                    v___x_5399_ = v___x_5393_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5397_);
                    v___x_5399_ = v_reuseFailAlloc_5400_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5374_ = v___x_5399_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5409_ == 0 {
                    v___x_5411_ = v___x_5408_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_ks_5405_);
                    lean_ctor_set(v_reuseFailAlloc_5425_, 1, v_vs_5406_);
                    v___x_5411_ = v_reuseFailAlloc_5425_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5412_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_5411_, v_x_5357_, v_x_5358_);
                v___x_5420_ = 7usize;
                v___x_5421_ = lean_usize_dec_le(v___x_5420_, v_x_5356_);
                if v___x_5421_ == 0 {
                    v___x_5422_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5412_);
                    v___x_5423_ = lean_unsigned_to_nat(4);
                    v___x_5424_ = lean_nat_dec_lt(v___x_5422_, v___x_5423_);
                    lean_dec(v___x_5422_);
                    v___y_5414_ = v___x_5424_;
                    state = 10;
                    continue;
                } else {
                    v___y_5414_ = v___x_5421_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5414_ == 0 {
                    v_ks_5415_ = lean_ctor_get(v_newNode_5412_, 0);
                    lean_inc_ref(v_ks_5415_);
                    v_vs_5416_ = lean_ctor_get(v_newNode_5412_, 1);
                    lean_inc_ref(v_vs_5416_);
                    lean_dec_ref(v_newNode_5412_);
                    v___x_5417_ = lean_unsigned_to_nat(0);
                    v___x_5418_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
                    v___x_5419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_5356_, v_ks_5415_, v_vs_5416_, v___x_5417_, v___x_5418_);
                    lean_dec_ref(v_vs_5416_);
                    lean_dec_ref(v_ks_5415_);
                    return v___x_5419_;
                } else {
                    return v_newNode_5412_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(
    mut v_depth_5427_: usize,
    mut v_keys_5428_: *mut LeanObject,
    mut v_vals_5429_: *mut LeanObject,
    mut v_i_5430_: *mut LeanObject,
    mut v_entries_5431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: u8 = 0;
    let mut v_k_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: u64 = 0;
    let mut v_h_5437_: usize = 0;
    let mut v___x_5438_: usize = 0;
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: usize = 0;
    let mut v___x_5441_: usize = 0;
    let mut v___x_5442_: usize = 0;
    let mut v_h_5443_: usize = 0;
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5432_ = lean_array_get_size(v_keys_5428_);
                v___x_5433_ = lean_nat_dec_lt(v_i_5430_, v___x_5432_);
                if v___x_5433_ == 0 {
                    lean_dec(v_i_5430_);
                    return v_entries_5431_;
                } else {
                    v_k_5434_ = lean_array_fget_borrowed(v_keys_5428_, v_i_5430_);
                    v_v_5435_ = lean_array_fget_borrowed(v_vals_5429_, v_i_5430_);
                    v___x_5436_ = l_Lean_instHashableMVarId_hash(v_k_5434_);
                    v_h_5437_ = lean_uint64_to_usize(v___x_5436_);
                    v___x_5438_ = 5usize;
                    v___x_5439_ = lean_unsigned_to_nat(1);
                    v___x_5440_ = 1usize;
                    v___x_5441_ = lean_usize_sub(v_depth_5427_, v___x_5440_);
                    v___x_5442_ = lean_usize_mul(v___x_5438_, v___x_5441_);
                    v_h_5443_ = lean_usize_shift_right(v_h_5437_, v___x_5442_);
                    v___x_5444_ = lean_nat_add(v_i_5430_, v___x_5439_);
                    lean_dec(v_i_5430_);
                    lean_inc(v_v_5435_);
                    lean_inc(v_k_5434_);
                    v___x_5445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_5431_, v_h_5443_, v_depth_5427_, v_k_5434_, v_v_5435_);
                    v_i_5430_ = v___x_5444_;
                    v_entries_5431_ = v___x_5445_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(
    mut v_depth_5447_: *mut LeanObject,
    mut v_keys_5448_: *mut LeanObject,
    mut v_vals_5449_: *mut LeanObject,
    mut v_i_5450_: *mut LeanObject,
    mut v_entries_5451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5452_: usize = 0;
    let mut v_res_5453_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5452_ = lean_unbox_usize(v_depth_5447_);
    lean_dec(v_depth_5447_);
    v_res_5453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_5452_, v_keys_5448_, v_vals_5449_, v_i_5450_, v_entries_5451_);
    lean_dec_ref(v_vals_5449_);
    lean_dec_ref(v_keys_5448_);
    return v_res_5453_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_5454_: *mut LeanObject,
    mut v_x_5455_: *mut LeanObject,
    mut v_x_5456_: *mut LeanObject,
    mut v_x_5457_: *mut LeanObject,
    mut v_x_5458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7242__boxed_5459_: usize = 0;
    let mut v_x_7243__boxed_5460_: usize = 0;
    let mut v_res_5461_: *mut LeanObject = core::ptr::null_mut();
    v_x_7242__boxed_5459_ = lean_unbox_usize(v_x_5455_);
    lean_dec(v_x_5455_);
    v_x_7243__boxed_5460_ = lean_unbox_usize(v_x_5456_);
    lean_dec(v_x_5456_);
    v_res_5461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_5454_, v_x_7242__boxed_5459_, v_x_7243__boxed_5460_, v_x_5457_, v_x_5458_);
    return v_res_5461_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(
    mut v_x_5462_: *mut LeanObject,
    mut v_x_5463_: *mut LeanObject,
    mut v_x_5464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5465_: u64 = 0;
    let mut v___x_5466_: usize = 0;
    let mut v___x_5467_: usize = 0;
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    v___x_5465_ = l_Lean_instHashableMVarId_hash(v_x_5463_);
    v___x_5466_ = lean_uint64_to_usize(v___x_5465_);
    v___x_5467_ = 1usize;
    v___x_5468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_5462_, v___x_5466_, v___x_5467_, v_x_5463_, v_x_5464_);
    return v___x_5468_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
    mut v_mvarId_5469_: *mut LeanObject,
    mut v_val_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5481_: u8 = 0;
    let mut v_depth_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5494_: u8 = 0;
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5505_: u8 = 0;
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5473_ = lean_st_ref_take(v___y_5471_);
                v_mctx_5474_ = lean_ctor_get(v___x_5473_, 0);
                v_cache_5475_ = lean_ctor_get(v___x_5473_, 1);
                v_zetaDeltaFVarIds_5476_ = lean_ctor_get(v___x_5473_, 2);
                v_postponed_5477_ = lean_ctor_get(v___x_5473_, 3);
                v_diag_5478_ = lean_ctor_get(v___x_5473_, 4);
                v_isSharedCheck_5506_ = (!lean_is_exclusive(v___x_5473_)) as u8;
                if v_isSharedCheck_5506_ == 0 {
                    v___x_5480_ = v___x_5473_;
                    v_isShared_5481_ = v_isSharedCheck_5506_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_5478_);
                    lean_inc(v_postponed_5477_);
                    lean_inc(v_zetaDeltaFVarIds_5476_);
                    lean_inc(v_cache_5475_);
                    lean_inc(v_mctx_5474_);
                    lean_dec(v___x_5473_);
                    v___x_5480_ = lean_box(0);
                    v_isShared_5481_ = v_isSharedCheck_5506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5482_ = lean_ctor_get(v_mctx_5474_, 0);
                v_levelAssignDepth_5483_ = lean_ctor_get(v_mctx_5474_, 1);
                v_lmvarCounter_5484_ = lean_ctor_get(v_mctx_5474_, 2);
                v_mvarCounter_5485_ = lean_ctor_get(v_mctx_5474_, 3);
                v_lDecls_5486_ = lean_ctor_get(v_mctx_5474_, 4);
                v_decls_5487_ = lean_ctor_get(v_mctx_5474_, 5);
                v_userNames_5488_ = lean_ctor_get(v_mctx_5474_, 6);
                v_lAssignment_5489_ = lean_ctor_get(v_mctx_5474_, 7);
                v_eAssignment_5490_ = lean_ctor_get(v_mctx_5474_, 8);
                v_dAssignment_5491_ = lean_ctor_get(v_mctx_5474_, 9);
                v_isSharedCheck_5505_ = (!lean_is_exclusive(v_mctx_5474_)) as u8;
                if v_isSharedCheck_5505_ == 0 {
                    v___x_5493_ = v_mctx_5474_;
                    v_isShared_5494_ = v_isSharedCheck_5505_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_5491_);
                    lean_inc(v_eAssignment_5490_);
                    lean_inc(v_lAssignment_5489_);
                    lean_inc(v_userNames_5488_);
                    lean_inc(v_decls_5487_);
                    lean_inc(v_lDecls_5486_);
                    lean_inc(v_mvarCounter_5485_);
                    lean_inc(v_lmvarCounter_5484_);
                    lean_inc(v_levelAssignDepth_5483_);
                    lean_inc(v_depth_5482_);
                    lean_dec(v_mctx_5474_);
                    v___x_5493_ = lean_box(0);
                    v_isShared_5494_ = v_isSharedCheck_5505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5495_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_5490_, v_mvarId_5469_, v_val_5470_);
                if v_isShared_5494_ == 0 {
                    lean_ctor_set(v___x_5493_, 8, v___x_5495_);
                    v___x_5497_ = v___x_5493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_depth_5482_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_levelAssignDepth_5483_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_lmvarCounter_5484_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_mvarCounter_5485_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_lDecls_5486_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 5, v_decls_5487_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 6, v_userNames_5488_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 7, v_lAssignment_5489_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 8, v___x_5495_);
                    lean_ctor_set(v_reuseFailAlloc_5504_, 9, v_dAssignment_5491_);
                    v___x_5497_ = v_reuseFailAlloc_5504_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5481_ == 0 {
                    lean_ctor_set(v___x_5480_, 0, v___x_5497_);
                    v___x_5499_ = v___x_5480_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5497_);
                    lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_cache_5475_);
                    lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_zetaDeltaFVarIds_5476_);
                    lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_postponed_5477_);
                    lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_diag_5478_);
                    v___x_5499_ = v_reuseFailAlloc_5503_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5500_ = lean_st_ref_set(v___y_5471_, v___x_5499_);
                v___x_5501_ = lean_box(0);
                v___x_5502_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5502_, 0, v___x_5501_);
                return v___x_5502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(
    mut v_mvarId_5507_: *mut LeanObject,
    mut v_val_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5511_: *mut LeanObject = core::ptr::null_mut();
    v_res_5511_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
        v_mvarId_5507_,
        v_val_5508_,
        v___y_5509_,
    );
    lean_dec(v___y_5509_);
    return v_res_5511_;
}
pub unsafe fn l_List_elem___at___00Lean_MVarId_apply_spec__2(
    mut v_a_5512_: *mut LeanObject,
    mut v_x_5513_: *mut LeanObject,
) -> u8 {
    let mut v___x_5514_: u8 = 0;
    let mut v_head_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5513_) == 0 {
                    v___x_5514_ = 0;
                    return v___x_5514_;
                } else {
                    v_head_5515_ = lean_ctor_get(v_x_5513_, 0);
                    v_tail_5516_ = lean_ctor_get(v_x_5513_, 1);
                    v___x_5517_ = l_Lean_instBEqMVarId_beq(v_a_5512_, v_head_5515_);
                    if v___x_5517_ == 0 {
                        v_x_5513_ = v_tail_5516_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5517_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(
    mut v_a_5519_: *mut LeanObject,
    mut v_x_5520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5521_: u8 = 0;
    let mut v_r_5522_: *mut LeanObject = core::ptr::null_mut();
    v_res_5521_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_5519_, v_x_5520_);
    lean_dec(v_x_5520_);
    lean_dec(v_a_5519_);
    v_r_5522_ = lean_box((v_res_5521_) as usize);
    return v_r_5522_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(
    mut v_a_5523_: *mut LeanObject,
    mut v_as_5524_: *mut LeanObject,
    mut v_i_5525_: usize,
    mut v_stop_5526_: usize,
    mut v_b_5527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: usize = 0;
    let mut v___x_5531_: usize = 0;
    let mut v___x_5533_: u8 = 0;
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: u8 = 0;
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5533_ = lean_usize_dec_eq(v_i_5525_, v_stop_5526_);
                if v___x_5533_ == 0 {
                    v___x_5534_ = lean_array_uget_borrowed(v_as_5524_, v_i_5525_);
                    v___x_5535_ =
                        l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_5534_, v_a_5523_);
                    if v___x_5535_ == 0 {
                        lean_inc(v___x_5534_);
                        v___x_5536_ = lean_array_push(v_b_5527_, v___x_5534_);
                        v___y_5529_ = v___x_5536_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5529_ = v_b_5527_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5527_;
                }
            }
            1 => {
                v___x_5530_ = 1usize;
                v___x_5531_ = lean_usize_add(v_i_5525_, v___x_5530_);
                v_i_5525_ = v___x_5531_;
                v_b_5527_ = v___y_5529_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(
    mut v_a_5537_: *mut LeanObject,
    mut v_as_5538_: *mut LeanObject,
    mut v_i_5539_: *mut LeanObject,
    mut v_stop_5540_: *mut LeanObject,
    mut v_b_5541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5542_: usize = 0;
    let mut v_stop_boxed_5543_: usize = 0;
    let mut v_res_5544_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5542_ = lean_unbox_usize(v_i_5539_);
    lean_dec(v_i_5539_);
    v_stop_boxed_5543_ = lean_unbox_usize(v_stop_5540_);
    lean_dec(v_stop_5540_);
    v_res_5544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_5537_, v_as_5538_, v_i_boxed_5542_, v_stop_boxed_5543_, v_b_5541_);
    lean_dec_ref(v_as_5538_);
    lean_dec(v_a_5537_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_MVarId_apply___lam__0(
    mut v_mvarId_5545_: *mut LeanObject,
    mut v___x_5546_: *mut LeanObject,
    mut v_e_5547_: *mut LeanObject,
    mut v_cfg_5548_: *mut LeanObject,
    mut v_term_x3f_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
    mut v___y_5552_: *mut LeanObject,
    mut v___y_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_unused_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5576_: u8 = 0;
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v___y_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5587_: u8 = 0;
    let mut v___y_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: u8 = 0;
    let mut v___x_5599_: u8 = 0;
    let mut v___x_5600_: usize = 0;
    let mut v___x_5601_: usize = 0;
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: usize = 0;
    let mut v___x_5604_: usize = 0;
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_a_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5621_: u8 = 0;
    let mut v___y_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5628_: u8 = 0;
    let mut v___y_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5636_: u8 = 0;
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5640_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rangeNumArgs_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newGoals_5657_: u8 = 0;
    let mut v_synthAssignedInstances_5658_: u8 = 0;
    let mut v_allowSynthFailures_5659_: u8 = 0;
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: u8 = 0;
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: usize = 0;
    let mut v___x_5674_: usize = 0;
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5679_: u8 = 0;
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5683_: u8 = 0;
    let mut v_a_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5691_: u8 = 0;
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: u8 = 0;
    let mut v_fst_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5711_: u8 = 0;
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5715_: u8 = 0;
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_unused_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5727_: u8 = 0;
    let mut v_unused_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5736_: u8 = 0;
    let mut v_a_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v_a_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5748_: u8 = 0;
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5752_: u8 = 0;
    let mut v_a_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_5546_);
                lean_inc(v_mvarId_5545_);
                v___x_5641_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5545_,
                    v___x_5546_,
                    v___y_5550_,
                    v___y_5551_,
                    v___y_5552_,
                    v___y_5553_,
                );
                if lean_obj_tag(v___x_5641_) == 0 {
                    lean_dec_ref_known(v___x_5641_, 1);
                    lean_inc(v_mvarId_5545_);
                    v___x_5642_ = l_Lean_MVarId_getType(
                        v_mvarId_5545_,
                        v___y_5550_,
                        v___y_5551_,
                        v___y_5552_,
                        v___y_5553_,
                    );
                    if lean_obj_tag(v___x_5642_) == 0 {
                        v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
                        lean_inc(v_a_5643_);
                        lean_dec_ref_known(v___x_5642_, 1);
                        lean_inc(v___y_5553_);
                        lean_inc_ref(v___y_5552_);
                        lean_inc(v___y_5551_);
                        lean_inc_ref(v___y_5550_);
                        lean_inc_ref(v_e_5547_);
                        v___x_5644_ = lean_infer_type(
                            v_e_5547_,
                            v___y_5550_,
                            v___y_5551_,
                            v___y_5552_,
                            v___y_5553_,
                        );
                        if lean_obj_tag(v___x_5644_) == 0 {
                            v_a_5645_ = lean_ctor_get(v___x_5644_, 0);
                            lean_inc_n(v_a_5645_, 2);
                            lean_dec_ref_known(v___x_5644_, 1);
                            v___x_5692_ = l_Lean_Meta_getExpectedNumArgsAux(
                                v_a_5645_,
                                v___y_5550_,
                                v___y_5551_,
                                v___y_5552_,
                                v___y_5553_,
                            );
                            if lean_obj_tag(v___x_5692_) == 0 {
                                v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
                                lean_inc(v_a_5693_);
                                lean_dec_ref_known(v___x_5692_, 1);
                                v_snd_5694_ = lean_ctor_get(v_a_5693_, 1);
                                v___x_5695_ = (lean_unbox(v_snd_5694_) as u8);
                                if v___x_5695_ == 0 {
                                    v_fst_5696_ = lean_ctor_get(v_a_5693_, 0);
                                    v_isSharedCheck_5716_ = (!lean_is_exclusive(v_a_5693_)) as u8;
                                    if v_isSharedCheck_5716_ == 0 {
                                        v_unused_5717_ = lean_ctor_get(v_a_5693_, 1);
                                        lean_dec(v_unused_5717_);
                                        v___x_5698_ = v_a_5693_;
                                        v_isShared_5699_ = v_isSharedCheck_5716_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_inc(v_fst_5696_);
                                        lean_dec(v_a_5693_);
                                        v___x_5698_ = lean_box(0);
                                        v_isShared_5699_ = v_isSharedCheck_5716_;
                                        state = 19;
                                        continue;
                                    }
                                } else {
                                    v_fst_5718_ = lean_ctor_get(v_a_5693_, 0);
                                    v_isSharedCheck_5727_ = (!lean_is_exclusive(v_a_5693_)) as u8;
                                    if v_isSharedCheck_5727_ == 0 {
                                        v_unused_5728_ = lean_ctor_get(v_a_5693_, 1);
                                        lean_dec(v_unused_5728_);
                                        v___x_5720_ = v_a_5693_;
                                        v_isShared_5721_ = v_isSharedCheck_5727_;
                                        state = 23;
                                        continue;
                                    } else {
                                        lean_inc(v_fst_5718_);
                                        lean_dec(v_a_5693_);
                                        v___x_5720_ = lean_box(0);
                                        v_isShared_5721_ = v_isSharedCheck_5727_;
                                        state = 23;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5645_);
                                lean_dec(v_a_5643_);
                                lean_dec(v___y_5553_);
                                lean_dec_ref(v___y_5552_);
                                lean_dec(v___y_5551_);
                                lean_dec_ref(v___y_5550_);
                                lean_dec(v_term_x3f_5549_);
                                lean_dec_ref(v_e_5547_);
                                lean_dec(v___x_5546_);
                                lean_dec(v_mvarId_5545_);
                                v_a_5729_ = lean_ctor_get(v___x_5692_, 0);
                                v_isSharedCheck_5736_ = (!lean_is_exclusive(v___x_5692_)) as u8;
                                if v_isSharedCheck_5736_ == 0 {
                                    v___x_5731_ = v___x_5692_;
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 25;
                                    continue;
                                } else {
                                    lean_inc(v_a_5729_);
                                    lean_dec(v___x_5692_);
                                    v___x_5731_ = lean_box(0);
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 25;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5643_);
                            lean_dec(v___y_5553_);
                            lean_dec_ref(v___y_5552_);
                            lean_dec(v___y_5551_);
                            lean_dec_ref(v___y_5550_);
                            lean_dec(v_term_x3f_5549_);
                            lean_dec_ref(v_e_5547_);
                            lean_dec(v___x_5546_);
                            lean_dec(v_mvarId_5545_);
                            v_a_5737_ = lean_ctor_get(v___x_5644_, 0);
                            v_isSharedCheck_5744_ = (!lean_is_exclusive(v___x_5644_)) as u8;
                            if v_isSharedCheck_5744_ == 0 {
                                v___x_5739_ = v___x_5644_;
                                v_isShared_5740_ = v_isSharedCheck_5744_;
                                state = 27;
                                continue;
                            } else {
                                lean_inc(v_a_5737_);
                                lean_dec(v___x_5644_);
                                v___x_5739_ = lean_box(0);
                                v_isShared_5740_ = v_isSharedCheck_5744_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_5553_);
                        lean_dec_ref(v___y_5552_);
                        lean_dec(v___y_5551_);
                        lean_dec_ref(v___y_5550_);
                        lean_dec(v_term_x3f_5549_);
                        lean_dec_ref(v_e_5547_);
                        lean_dec(v___x_5546_);
                        lean_dec(v_mvarId_5545_);
                        v_a_5745_ = lean_ctor_get(v___x_5642_, 0);
                        v_isSharedCheck_5752_ = (!lean_is_exclusive(v___x_5642_)) as u8;
                        if v_isSharedCheck_5752_ == 0 {
                            v___x_5747_ = v___x_5642_;
                            v_isShared_5748_ = v_isSharedCheck_5752_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_5745_);
                            lean_dec(v___x_5642_);
                            v___x_5747_ = lean_box(0);
                            v_isShared_5748_ = v_isSharedCheck_5752_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5553_);
                    lean_dec_ref(v___y_5552_);
                    lean_dec(v___y_5551_);
                    lean_dec_ref(v___y_5550_);
                    lean_dec(v_term_x3f_5549_);
                    lean_dec_ref(v_e_5547_);
                    lean_dec(v___x_5546_);
                    lean_dec(v_mvarId_5545_);
                    v_a_5753_ = lean_ctor_get(v___x_5641_, 0);
                    v_isSharedCheck_5760_ = (!lean_is_exclusive(v___x_5641_)) as u8;
                    if v_isSharedCheck_5760_ == 0 {
                        v___x_5755_ = v___x_5641_;
                        v_isShared_5756_ = v_isSharedCheck_5760_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_5753_);
                        lean_dec(v___x_5641_);
                        v___x_5755_ = lean_box(0);
                        v_isShared_5756_ = v_isSharedCheck_5760_;
                        state = 31;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5562_ = lean_array_to_list(v___y_5561_);
                v___x_5563_ = l_List_appendTR___redArg(v___y_5559_, v___x_5562_);
                lean_inc(v___x_5563_);
                v___x_5564_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(
                    v___x_5563_,
                    v___y_5560_,
                    v___y_5558_,
                    v___y_5557_,
                    v___y_5556_,
                );
                lean_dec(v___y_5556_);
                lean_dec_ref(v___y_5557_);
                lean_dec(v___y_5558_);
                lean_dec_ref(v___y_5560_);
                if lean_obj_tag(v___x_5564_) == 0 {
                    v_isSharedCheck_5571_ = (!lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5571_ == 0 {
                        v_unused_5572_ = lean_ctor_get(v___x_5564_, 0);
                        lean_dec(v_unused_5572_);
                        v___x_5566_ = v___x_5564_;
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_5564_);
                        v___x_5566_ = lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5563_);
                    v_a_5573_ = lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5580_ = (!lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5580_ == 0 {
                        v___x_5575_ = v___x_5564_;
                        v_isShared_5576_ = v_isSharedCheck_5580_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5573_);
                        lean_dec(v___x_5564_);
                        v___x_5575_ = lean_box(0);
                        v_isShared_5576_ = v_isSharedCheck_5580_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5567_ == 0 {
                    lean_ctor_set(v___x_5566_, 0, v___x_5563_);
                    v___x_5569_ = v___x_5566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5563_);
                    v___x_5569_ = v_reuseFailAlloc_5570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5569_;
            }
            4 => {
                if v_isShared_5576_ == 0 {
                    v___x_5578_ = v___x_5575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
                    v___x_5578_ = v_reuseFailAlloc_5579_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5578_;
            }
            6 => {
                v___x_5591_ = l_Lean_Meta_appendParentTag(
                    v_mvarId_5545_,
                    v_a_5590_,
                    v___y_5588_,
                    v___y_5589_,
                    v___y_5586_,
                    v___y_5585_,
                    v___y_5582_,
                );
                lean_dec_ref(v___y_5588_);
                if lean_obj_tag(v___x_5591_) == 0 {
                    lean_dec_ref_known(v___x_5591_, 1);
                    v___x_5592_ = l_Lean_Meta_getMVarsNoDelayed(
                        v___y_5584_,
                        v___y_5589_,
                        v___y_5586_,
                        v___y_5585_,
                        v___y_5582_,
                    );
                    if lean_obj_tag(v___x_5592_) == 0 {
                        v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
                        lean_inc(v_a_5593_);
                        lean_dec_ref_known(v___x_5592_, 1);
                        v___x_5594_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(
                            v_a_5590_,
                            v___y_5587_,
                            v___y_5589_,
                            v___y_5586_,
                            v___y_5585_,
                            v___y_5582_,
                        );
                        if lean_obj_tag(v___x_5594_) == 0 {
                            v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
                            lean_inc(v_a_5595_);
                            lean_dec_ref_known(v___x_5594_, 1);
                            v___x_5596_ = lean_array_get_size(v_a_5593_);
                            v___x_5597_ = lean_mk_empty_array_with_capacity(v___y_5583_);
                            v___x_5598_ = lean_nat_dec_lt(v___y_5583_, v___x_5596_);
                            if v___x_5598_ == 0 {
                                lean_dec(v_a_5593_);
                                v___y_5556_ = v___y_5582_;
                                v___y_5557_ = v___y_5585_;
                                v___y_5558_ = v___y_5586_;
                                v___y_5559_ = v_a_5595_;
                                v___y_5560_ = v___y_5589_;
                                v___y_5561_ = v___x_5597_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5599_ = lean_nat_dec_le(v___x_5596_, v___x_5596_);
                                if v___x_5599_ == 0 {
                                    if v___x_5598_ == 0 {
                                        lean_dec(v_a_5593_);
                                        v___y_5556_ = v___y_5582_;
                                        v___y_5557_ = v___y_5585_;
                                        v___y_5558_ = v___y_5586_;
                                        v___y_5559_ = v_a_5595_;
                                        v___y_5560_ = v___y_5589_;
                                        v___y_5561_ = v___x_5597_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_5600_ = 0usize;
                                        v___x_5601_ = lean_usize_of_nat(v___x_5596_);
                                        v___x_5602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_5595_, v_a_5593_, v___x_5600_, v___x_5601_, v___x_5597_);
                                        lean_dec(v_a_5593_);
                                        v___y_5556_ = v___y_5582_;
                                        v___y_5557_ = v___y_5585_;
                                        v___y_5558_ = v___y_5586_;
                                        v___y_5559_ = v_a_5595_;
                                        v___y_5560_ = v___y_5589_;
                                        v___y_5561_ = v___x_5602_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_5603_ = 0usize;
                                    v___x_5604_ = lean_usize_of_nat(v___x_5596_);
                                    v___x_5605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_5595_, v_a_5593_, v___x_5603_, v___x_5604_, v___x_5597_);
                                    lean_dec(v_a_5593_);
                                    v___y_5556_ = v___y_5582_;
                                    v___y_5557_ = v___y_5585_;
                                    v___y_5558_ = v___y_5586_;
                                    v___y_5559_ = v_a_5595_;
                                    v___y_5560_ = v___y_5589_;
                                    v___y_5561_ = v___x_5605_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5593_);
                            lean_dec_ref(v___y_5589_);
                            lean_dec(v___y_5586_);
                            lean_dec_ref(v___y_5585_);
                            lean_dec(v___y_5582_);
                            return v___x_5594_;
                        }
                    } else {
                        lean_dec_ref(v_a_5590_);
                        lean_dec_ref(v___y_5589_);
                        lean_dec(v___y_5586_);
                        lean_dec_ref(v___y_5585_);
                        lean_dec(v___y_5582_);
                        v_a_5606_ = lean_ctor_get(v___x_5592_, 0);
                        v_isSharedCheck_5613_ = (!lean_is_exclusive(v___x_5592_)) as u8;
                        if v_isSharedCheck_5613_ == 0 {
                            v___x_5608_ = v___x_5592_;
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5606_);
                            lean_dec(v___x_5592_);
                            v___x_5608_ = lean_box(0);
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_5590_);
                    lean_dec_ref(v___y_5589_);
                    lean_dec(v___y_5586_);
                    lean_dec_ref(v___y_5585_);
                    lean_dec_ref(v___y_5584_);
                    lean_dec(v___y_5582_);
                    v_a_5614_ = lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5621_ = (!lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5621_ == 0 {
                        v___x_5616_ = v___x_5591_;
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5614_);
                        lean_dec(v___x_5591_);
                        v___x_5616_ = lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5609_ == 0 {
                    v___x_5611_ = v___x_5608_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5611_;
            }
            9 => {
                if v_isShared_5617_ == 0 {
                    v___x_5619_ = v___x_5616_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
                    v___x_5619_ = v_reuseFailAlloc_5620_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5619_;
            }
            11 => {
                if lean_obj_tag(v___y_5631_) == 0 {
                    v_a_5632_ = lean_ctor_get(v___y_5631_, 0);
                    lean_inc(v_a_5632_);
                    lean_dec_ref_known(v___y_5631_, 1);
                    v___y_5582_ = v___y_5623_;
                    v___y_5583_ = v___y_5624_;
                    v___y_5584_ = v___y_5625_;
                    v___y_5585_ = v___y_5626_;
                    v___y_5586_ = v___y_5627_;
                    v___y_5587_ = v___y_5628_;
                    v___y_5588_ = v___y_5629_;
                    v___y_5589_ = v___y_5630_;
                    v_a_5590_ = v_a_5632_;
                    state = 6;
                    continue;
                } else {
                    lean_dec_ref(v___y_5630_);
                    lean_dec_ref(v___y_5629_);
                    lean_dec(v___y_5627_);
                    lean_dec_ref(v___y_5626_);
                    lean_dec_ref(v___y_5625_);
                    lean_dec(v___y_5623_);
                    lean_dec(v_mvarId_5545_);
                    v_a_5633_ = lean_ctor_get(v___y_5631_, 0);
                    v_isSharedCheck_5640_ = (!lean_is_exclusive(v___y_5631_)) as u8;
                    if v_isSharedCheck_5640_ == 0 {
                        v___x_5635_ = v___y_5631_;
                        v_isShared_5636_ = v_isSharedCheck_5640_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5633_);
                        lean_dec(v___y_5631_);
                        v___x_5635_ = lean_box(0);
                        v_isShared_5636_ = v_isSharedCheck_5640_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_5636_ == 0 {
                    v___x_5638_ = v___x_5635_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_a_5633_);
                    v___x_5638_ = v_reuseFailAlloc_5639_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5638_;
            }
            14 => {
                lean_inc(v_mvarId_5545_);
                v___x_5653_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(
                    v_mvarId_5545_,
                    v_cfg_5548_,
                    v_term_x3f_5549_,
                    v_a_5643_,
                    v_a_5645_,
                    v_rangeNumArgs_5647_,
                    v_lower_5648_,
                    v___y_5649_,
                    v___y_5650_,
                    v___y_5651_,
                    v___y_5652_,
                );
                lean_dec_ref(v_rangeNumArgs_5647_);
                if lean_obj_tag(v___x_5653_) == 0 {
                    v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
                    lean_inc(v_a_5654_);
                    lean_dec_ref_known(v___x_5653_, 1);
                    v_fst_5655_ = lean_ctor_get(v_a_5654_, 0);
                    lean_inc(v_fst_5655_);
                    v_snd_5656_ = lean_ctor_get(v_a_5654_, 1);
                    lean_inc_n(v_snd_5656_, 2);
                    lean_dec(v_a_5654_);
                    v_newGoals_5657_ = lean_ctor_get_uint8(v_cfg_5548_, 0 as u32);
                    v_synthAssignedInstances_5658_ = lean_ctor_get_uint8(v_cfg_5548_, 1 as u32);
                    v_allowSynthFailures_5659_ = lean_ctor_get_uint8(v_cfg_5548_, 2 as u32);
                    lean_inc(v_mvarId_5545_);
                    v___x_5660_ = l_Lean_Meta_synthAppInstances(
                        v___x_5546_,
                        v_mvarId_5545_,
                        v_fst_5655_,
                        v_snd_5656_,
                        v_synthAssignedInstances_5658_,
                        v_allowSynthFailures_5659_,
                        v___y_5649_,
                        v___y_5650_,
                        v___y_5651_,
                        v___y_5652_,
                    );
                    if lean_obj_tag(v___x_5660_) == 0 {
                        lean_dec_ref_known(v___x_5660_, 1);
                        v___x_5661_ =
                            l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(
                                v_e_5547_,
                                v___y_5650_,
                            );
                        v_a_5662_ = lean_ctor_get(v___x_5661_, 0);
                        lean_inc_n(v_a_5662_, 2);
                        lean_dec_ref(v___x_5661_);
                        v___x_5663_ = l_Lean_mkAppN(v_a_5662_, v_fst_5655_);
                        lean_inc(v_mvarId_5545_);
                        v___x_5664_ =
                            l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                v_mvarId_5545_,
                                v___x_5663_,
                                v___y_5650_,
                            );
                        lean_dec_ref(v___x_5664_);
                        v___x_5665_ = lean_unsigned_to_nat(0);
                        v___x_5666_ = lean_array_get_size(v_fst_5655_);
                        v___x_5667_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0;
                        v___x_5668_ = lean_nat_dec_lt(v___x_5665_, v___x_5666_);
                        if v___x_5668_ == 0 {
                            lean_dec(v_fst_5655_);
                            v___y_5582_ = v___y_5652_;
                            v___y_5583_ = v___x_5665_;
                            v___y_5584_ = v_a_5662_;
                            v___y_5585_ = v___y_5651_;
                            v___y_5586_ = v___y_5650_;
                            v___y_5587_ = v_newGoals_5657_;
                            v___y_5588_ = v_snd_5656_;
                            v___y_5589_ = v___y_5649_;
                            v_a_5590_ = v___x_5667_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5669_ = lean_nat_dec_le(v___x_5666_, v___x_5666_);
                            if v___x_5669_ == 0 {
                                if v___x_5668_ == 0 {
                                    lean_dec(v_fst_5655_);
                                    v___y_5582_ = v___y_5652_;
                                    v___y_5583_ = v___x_5665_;
                                    v___y_5584_ = v_a_5662_;
                                    v___y_5585_ = v___y_5651_;
                                    v___y_5586_ = v___y_5650_;
                                    v___y_5587_ = v_newGoals_5657_;
                                    v___y_5588_ = v_snd_5656_;
                                    v___y_5589_ = v___y_5649_;
                                    v_a_5590_ = v___x_5667_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_5670_ = 0usize;
                                    v___x_5671_ = lean_usize_of_nat(v___x_5666_);
                                    v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_5655_, v___x_5670_, v___x_5671_, v___x_5667_, v___y_5650_);
                                    lean_dec(v_fst_5655_);
                                    v___y_5623_ = v___y_5652_;
                                    v___y_5624_ = v___x_5665_;
                                    v___y_5625_ = v_a_5662_;
                                    v___y_5626_ = v___y_5651_;
                                    v___y_5627_ = v___y_5650_;
                                    v___y_5628_ = v_newGoals_5657_;
                                    v___y_5629_ = v_snd_5656_;
                                    v___y_5630_ = v___y_5649_;
                                    v___y_5631_ = v___x_5672_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                v___x_5673_ = 0usize;
                                v___x_5674_ = lean_usize_of_nat(v___x_5666_);
                                v___x_5675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_5655_, v___x_5673_, v___x_5674_, v___x_5667_, v___y_5650_);
                                lean_dec(v_fst_5655_);
                                v___y_5623_ = v___y_5652_;
                                v___y_5624_ = v___x_5665_;
                                v___y_5625_ = v_a_5662_;
                                v___y_5626_ = v___y_5651_;
                                v___y_5627_ = v___y_5650_;
                                v___y_5628_ = v_newGoals_5657_;
                                v___y_5629_ = v_snd_5656_;
                                v___y_5630_ = v___y_5649_;
                                v___y_5631_ = v___x_5675_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_5656_);
                        lean_dec(v_fst_5655_);
                        lean_dec(v___y_5652_);
                        lean_dec_ref(v___y_5651_);
                        lean_dec(v___y_5650_);
                        lean_dec_ref(v___y_5649_);
                        lean_dec_ref(v_e_5547_);
                        lean_dec(v_mvarId_5545_);
                        v_a_5676_ = lean_ctor_get(v___x_5660_, 0);
                        v_isSharedCheck_5683_ = (!lean_is_exclusive(v___x_5660_)) as u8;
                        if v_isSharedCheck_5683_ == 0 {
                            v___x_5678_ = v___x_5660_;
                            v_isShared_5679_ = v_isSharedCheck_5683_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5676_);
                            lean_dec(v___x_5660_);
                            v___x_5678_ = lean_box(0);
                            v_isShared_5679_ = v_isSharedCheck_5683_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5652_);
                    lean_dec_ref(v___y_5651_);
                    lean_dec(v___y_5650_);
                    lean_dec_ref(v___y_5649_);
                    lean_dec_ref(v_e_5547_);
                    lean_dec(v___x_5546_);
                    lean_dec(v_mvarId_5545_);
                    v_a_5684_ = lean_ctor_get(v___x_5653_, 0);
                    v_isSharedCheck_5691_ = (!lean_is_exclusive(v___x_5653_)) as u8;
                    if v_isSharedCheck_5691_ == 0 {
                        v___x_5686_ = v___x_5653_;
                        v_isShared_5687_ = v_isSharedCheck_5691_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5684_);
                        lean_dec(v___x_5653_);
                        v___x_5686_ = lean_box(0);
                        v_isShared_5687_ = v_isSharedCheck_5691_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5679_ == 0 {
                    v___x_5681_ = v___x_5678_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5676_);
                    v___x_5681_ = v_reuseFailAlloc_5682_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5681_;
            }
            17 => {
                if v_isShared_5687_ == 0 {
                    v___x_5689_ = v___x_5686_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_a_5684_);
                    v___x_5689_ = v_reuseFailAlloc_5690_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5689_;
            }
            19 => {
                lean_inc(v_a_5643_);
                v___x_5700_ = l_Lean_Meta_getExpectedNumArgs(
                    v_a_5643_,
                    v___y_5550_,
                    v___y_5551_,
                    v___y_5552_,
                    v___y_5553_,
                );
                if lean_obj_tag(v___x_5700_) == 0 {
                    v_a_5701_ = lean_ctor_get(v___x_5700_, 0);
                    lean_inc(v_a_5701_);
                    lean_dec_ref_known(v___x_5700_, 1);
                    v___x_5702_ = lean_nat_sub(v_fst_5696_, v_a_5701_);
                    lean_dec(v_a_5701_);
                    v___x_5703_ = lean_unsigned_to_nat(1);
                    v___x_5704_ = lean_nat_add(v_fst_5696_, v___x_5703_);
                    lean_dec(v_fst_5696_);
                    lean_inc(v___x_5702_);
                    if v_isShared_5699_ == 0 {
                        lean_ctor_set(v___x_5698_, 1, v___x_5704_);
                        lean_ctor_set(v___x_5698_, 0, v___x_5702_);
                        v___x_5706_ = v___x_5698_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5707_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5707_, 0, v___x_5702_);
                        lean_ctor_set(v_reuseFailAlloc_5707_, 1, v___x_5704_);
                        v___x_5706_ = v_reuseFailAlloc_5707_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5698_);
                    lean_dec(v_fst_5696_);
                    lean_dec(v_a_5645_);
                    lean_dec(v_a_5643_);
                    lean_dec(v___y_5553_);
                    lean_dec_ref(v___y_5552_);
                    lean_dec(v___y_5551_);
                    lean_dec_ref(v___y_5550_);
                    lean_dec(v_term_x3f_5549_);
                    lean_dec_ref(v_e_5547_);
                    lean_dec(v___x_5546_);
                    lean_dec(v_mvarId_5545_);
                    v_a_5708_ = lean_ctor_get(v___x_5700_, 0);
                    v_isSharedCheck_5715_ = (!lean_is_exclusive(v___x_5700_)) as u8;
                    if v_isSharedCheck_5715_ == 0 {
                        v___x_5710_ = v___x_5700_;
                        v_isShared_5711_ = v_isSharedCheck_5715_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_5708_);
                        lean_dec(v___x_5700_);
                        v___x_5710_ = lean_box(0);
                        v_isShared_5711_ = v_isSharedCheck_5715_;
                        state = 21;
                        continue;
                    }
                }
            }
            20 => {
                v_rangeNumArgs_5647_ = v___x_5706_;
                v_lower_5648_ = v___x_5702_;
                v___y_5649_ = v___y_5550_;
                v___y_5650_ = v___y_5551_;
                v___y_5651_ = v___y_5552_;
                v___y_5652_ = v___y_5553_;
                state = 14;
                continue;
            }
            21 => {
                if v_isShared_5711_ == 0 {
                    v___x_5713_ = v___x_5710_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_a_5708_);
                    v___x_5713_ = v_reuseFailAlloc_5714_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5713_;
            }
            23 => {
                v___x_5722_ = lean_unsigned_to_nat(1);
                v___x_5723_ = lean_nat_add(v_fst_5718_, v___x_5722_);
                lean_inc(v_fst_5718_);
                if v_isShared_5721_ == 0 {
                    lean_ctor_set(v___x_5720_, 1, v___x_5723_);
                    v___x_5725_ = v___x_5720_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_fst_5718_);
                    lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5723_);
                    v___x_5725_ = v_reuseFailAlloc_5726_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_rangeNumArgs_5647_ = v___x_5725_;
                v_lower_5648_ = v_fst_5718_;
                v___y_5649_ = v___y_5550_;
                v___y_5650_ = v___y_5551_;
                v___y_5651_ = v___y_5552_;
                v___y_5652_ = v___y_5553_;
                state = 14;
                continue;
            }
            25 => {
                if v_isShared_5732_ == 0 {
                    v___x_5734_ = v___x_5731_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5734_;
            }
            27 => {
                if v_isShared_5740_ == 0 {
                    v___x_5742_ = v___x_5739_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5742_;
            }
            29 => {
                if v_isShared_5748_ == 0 {
                    v___x_5750_ = v___x_5747_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
                    v___x_5750_ = v_reuseFailAlloc_5751_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5750_;
            }
            31 => {
                if v_isShared_5756_ == 0 {
                    v___x_5758_ = v___x_5755_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_apply___lam__0___boxed(
    mut v_mvarId_5761_: *mut LeanObject,
    mut v___x_5762_: *mut LeanObject,
    mut v_e_5763_: *mut LeanObject,
    mut v_cfg_5764_: *mut LeanObject,
    mut v_term_x3f_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5771_: *mut LeanObject = core::ptr::null_mut();
    v_res_5771_ = l_Lean_MVarId_apply___lam__0(
        v_mvarId_5761_,
        v___x_5762_,
        v_e_5763_,
        v_cfg_5764_,
        v_term_x3f_5765_,
        v___y_5766_,
        v___y_5767_,
        v___y_5768_,
        v___y_5769_,
    );
    lean_dec_ref(v_cfg_5764_);
    return v_res_5771_;
}
pub unsafe fn l_Lean_MVarId_apply(
    mut v_mvarId_5772_: *mut LeanObject,
    mut v_e_5773_: *mut LeanObject,
    mut v_cfg_5774_: *mut LeanObject,
    mut v_term_x3f_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
    mut v_a_5777_: *mut LeanObject,
    mut v_a_5778_: *mut LeanObject,
    mut v_a_5779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    v___x_5781_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
    lean_inc(v_mvarId_5772_);
    v___f_5782_ = lean_alloc_closure(
        l_Lean_MVarId_apply___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_5782_, 0, v_mvarId_5772_);
    lean_closure_set(v___f_5782_, 1, v___x_5781_);
    lean_closure_set(v___f_5782_, 2, v_e_5773_);
    lean_closure_set(v___f_5782_, 3, v_cfg_5774_);
    lean_closure_set(v___f_5782_, 4, v_term_x3f_5775_);
    v___x_5783_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_5772_,
        v___f_5782_,
        v_a_5776_,
        v_a_5777_,
        v_a_5778_,
        v_a_5779_,
    );
    return v___x_5783_;
}
pub unsafe fn l_Lean_MVarId_apply___boxed(
    mut v_mvarId_5784_: *mut LeanObject,
    mut v_e_5785_: *mut LeanObject,
    mut v_cfg_5786_: *mut LeanObject,
    mut v_term_x3f_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
    mut v_a_5789_: *mut LeanObject,
    mut v_a_5790_: *mut LeanObject,
    mut v_a_5791_: *mut LeanObject,
    mut v_a_5792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5793_: *mut LeanObject = core::ptr::null_mut();
    v_res_5793_ = l_Lean_MVarId_apply(
        v_mvarId_5784_,
        v_e_5785_,
        v_cfg_5786_,
        v_term_x3f_5787_,
        v_a_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
    );
    lean_dec(v_a_5791_);
    lean_dec_ref(v_a_5790_);
    lean_dec(v_a_5789_);
    lean_dec_ref(v_a_5788_);
    return v_res_5793_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(
    mut v_mvarId_5794_: *mut LeanObject,
    mut v_val_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    v___x_5801_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
        v_mvarId_5794_,
        v_val_5795_,
        v___y_5797_,
    );
    return v___x_5801_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(
    mut v_mvarId_5802_: *mut LeanObject,
    mut v_val_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
    mut v___y_5808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5809_: *mut LeanObject = core::ptr::null_mut();
    v_res_5809_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(
        v_mvarId_5802_,
        v_val_5803_,
        v___y_5804_,
        v___y_5805_,
        v___y_5806_,
        v___y_5807_,
    );
    lean_dec(v___y_5807_);
    lean_dec_ref(v___y_5806_);
    lean_dec(v___y_5805_);
    lean_dec_ref(v___y_5804_);
    return v_res_5809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(
    mut v_as_5810_: *mut LeanObject,
    mut v_i_5811_: usize,
    mut v_stop_5812_: usize,
    mut v_b_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    v___x_5819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_5810_, v_i_5811_, v_stop_5812_, v_b_5813_, v___y_5815_);
    return v___x_5819_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(
    mut v_as_5820_: *mut LeanObject,
    mut v_i_5821_: *mut LeanObject,
    mut v_stop_5822_: *mut LeanObject,
    mut v_b_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
    mut v___y_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5829_: usize = 0;
    let mut v_stop_boxed_5830_: usize = 0;
    let mut v_res_5831_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5829_ = lean_unbox_usize(v_i_5821_);
    lean_dec(v_i_5821_);
    v_stop_boxed_5830_ = lean_unbox_usize(v_stop_5822_);
    lean_dec(v_stop_5822_);
    v_res_5831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_5820_, v_i_boxed_5829_, v_stop_boxed_5830_, v_b_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
    lean_dec(v___y_5827_);
    lean_dec_ref(v___y_5826_);
    lean_dec(v___y_5825_);
    lean_dec_ref(v___y_5824_);
    lean_dec_ref(v_as_5820_);
    return v_res_5831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(
    mut v_00_u03b2_5832_: *mut LeanObject,
    mut v_x_5833_: *mut LeanObject,
    mut v_x_5834_: *mut LeanObject,
    mut v_x_5835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    v___x_5836_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_5833_, v_x_5834_, v_x_5835_);
    return v___x_5836_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(
    mut v_00_u03b2_5837_: *mut LeanObject,
    mut v_x_5838_: *mut LeanObject,
    mut v_x_5839_: usize,
    mut v_x_5840_: usize,
    mut v_x_5841_: *mut LeanObject,
    mut v_x_5842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    v___x_5843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_5838_, v_x_5839_, v_x_5840_, v_x_5841_, v_x_5842_);
    return v___x_5843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_5844_: *mut LeanObject,
    mut v_x_5845_: *mut LeanObject,
    mut v_x_5846_: *mut LeanObject,
    mut v_x_5847_: *mut LeanObject,
    mut v_x_5848_: *mut LeanObject,
    mut v_x_5849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7975__boxed_5850_: usize = 0;
    let mut v_x_7976__boxed_5851_: usize = 0;
    let mut v_res_5852_: *mut LeanObject = core::ptr::null_mut();
    v_x_7975__boxed_5850_ = lean_unbox_usize(v_x_5846_);
    lean_dec(v_x_5846_);
    v_x_7976__boxed_5851_ = lean_unbox_usize(v_x_5847_);
    lean_dec(v_x_5847_);
    v_res_5852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_5844_, v_x_5845_, v_x_7975__boxed_5850_, v_x_7976__boxed_5851_, v_x_5848_, v_x_5849_);
    return v_res_5852_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(
    mut v_00_u03b2_5853_: *mut LeanObject,
    mut v_n_5854_: *mut LeanObject,
    mut v_k_5855_: *mut LeanObject,
    mut v_v_5856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    v___x_5857_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_5854_, v_k_5855_, v_v_5856_);
    return v___x_5857_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(
    mut v_00_u03b2_5858_: *mut LeanObject,
    mut v_depth_5859_: usize,
    mut v_keys_5860_: *mut LeanObject,
    mut v_vals_5861_: *mut LeanObject,
    mut v_heq_5862_: *mut LeanObject,
    mut v_i_5863_: *mut LeanObject,
    mut v_entries_5864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    v___x_5865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_5859_, v_keys_5860_, v_vals_5861_, v_i_5863_, v_entries_5864_);
    return v___x_5865_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(
    mut v_00_u03b2_5866_: *mut LeanObject,
    mut v_depth_5867_: *mut LeanObject,
    mut v_keys_5868_: *mut LeanObject,
    mut v_vals_5869_: *mut LeanObject,
    mut v_heq_5870_: *mut LeanObject,
    mut v_i_5871_: *mut LeanObject,
    mut v_entries_5872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5873_: usize = 0;
    let mut v_res_5874_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5873_ = lean_unbox_usize(v_depth_5867_);
    lean_dec(v_depth_5867_);
    v_res_5874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_5866_, v_depth_boxed_5873_, v_keys_5868_, v_vals_5869_, v_heq_5870_, v_i_5871_, v_entries_5872_);
    lean_dec_ref(v_vals_5869_);
    lean_dec_ref(v_keys_5868_);
    return v_res_5874_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(
    mut v_00_u03b2_5875_: *mut LeanObject,
    mut v_x_5876_: *mut LeanObject,
    mut v_x_5877_: *mut LeanObject,
    mut v_x_5878_: *mut LeanObject,
    mut v_x_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    v___x_5880_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_5876_, v_x_5877_, v_x_5878_, v_x_5879_);
    return v___x_5880_;
}
pub unsafe fn _init_l_Lean_MVarId_applyConst___closed__1() -> *mut LeanObject {
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    v___x_5882_ = l_Lean_MVarId_applyConst___closed__0;
    v___x_5883_ = l_Lean_stringToMessageData(v___x_5882_);
    return v___x_5883_;
}
pub unsafe fn l_Lean_MVarId_applyConst(
    mut v_mvar_5884_: *mut LeanObject,
    mut v_c_5885_: *mut LeanObject,
    mut v_cfg_5886_: *mut LeanObject,
    mut v_a_5887_: *mut LeanObject,
    mut v_a_5888_: *mut LeanObject,
    mut v_a_5889_: *mut LeanObject,
    mut v_a_5890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: u8 = 0;
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5904_: u8 = 0;
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_c_5885_);
                v___x_5892_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v_c_5885_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_,
                );
                if lean_obj_tag(v___x_5892_) == 0 {
                    v_a_5893_ = lean_ctor_get(v___x_5892_, 0);
                    lean_inc(v_a_5893_);
                    lean_dec_ref_known(v___x_5892_, 1);
                    v___x_5894_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyConst___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyConst___closed__1_once),
                        _init_l_Lean_MVarId_applyConst___closed__1,
                    );
                    v___x_5895_ = 0;
                    v___x_5896_ = l_Lean_MessageData_ofConstName(v_c_5885_, v___x_5895_);
                    v___x_5897_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5897_, 0, v___x_5894_);
                    lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                    v___x_5898_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5898_, 0, v___x_5897_);
                    lean_ctor_set(v___x_5898_, 1, v___x_5894_);
                    v___x_5899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5899_, 0, v___x_5898_);
                    v___x_5900_ = l_Lean_MVarId_apply(
                        v_mvar_5884_,
                        v_a_5893_,
                        v_cfg_5886_,
                        v___x_5899_,
                        v_a_5887_,
                        v_a_5888_,
                        v_a_5889_,
                        v_a_5890_,
                    );
                    return v___x_5900_;
                } else {
                    lean_dec_ref(v_cfg_5886_);
                    lean_dec(v_c_5885_);
                    lean_dec(v_mvar_5884_);
                    v_a_5901_ = lean_ctor_get(v___x_5892_, 0);
                    v_isSharedCheck_5908_ = (!lean_is_exclusive(v___x_5892_)) as u8;
                    if v_isSharedCheck_5908_ == 0 {
                        v___x_5903_ = v___x_5892_;
                        v_isShared_5904_ = v_isSharedCheck_5908_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5901_);
                        lean_dec(v___x_5892_);
                        v___x_5903_ = lean_box(0);
                        v_isShared_5904_ = v_isSharedCheck_5908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5904_ == 0 {
                    v___x_5906_ = v___x_5903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5907_, 0, v_a_5901_);
                    v___x_5906_ = v_reuseFailAlloc_5907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyConst___boxed(
    mut v_mvar_5909_: *mut LeanObject,
    mut v_c_5910_: *mut LeanObject,
    mut v_cfg_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
    mut v_a_5913_: *mut LeanObject,
    mut v_a_5914_: *mut LeanObject,
    mut v_a_5915_: *mut LeanObject,
    mut v_a_5916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5917_: *mut LeanObject = core::ptr::null_mut();
    v_res_5917_ = l_Lean_MVarId_applyConst(
        v_mvar_5909_,
        v_c_5910_,
        v_cfg_5911_,
        v_a_5912_,
        v_a_5913_,
        v_a_5914_,
        v_a_5915_,
    );
    lean_dec(v_a_5915_);
    lean_dec_ref(v_a_5914_);
    lean_dec(v_a_5913_);
    lean_dec_ref(v_a_5912_);
    return v_res_5917_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(
    mut v_msgData_5918_: *mut LeanObject,
    mut v___y_5919_: *mut LeanObject,
    mut v___y_5920_: *mut LeanObject,
    mut v___y_5921_: *mut LeanObject,
    mut v___y_5922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    v___x_5924_ = lean_st_ref_get(v___y_5922_);
    v_env_5925_ = lean_ctor_get(v___x_5924_, 0);
    lean_inc_ref(v_env_5925_);
    lean_dec(v___x_5924_);
    v___x_5926_ = lean_st_ref_get(v___y_5920_);
    v_mctx_5927_ = lean_ctor_get(v___x_5926_, 0);
    lean_inc_ref(v_mctx_5927_);
    lean_dec(v___x_5926_);
    v_lctx_5928_ = lean_ctor_get(v___y_5919_, 2);
    v_options_5929_ = lean_ctor_get(v___y_5921_, 2);
    lean_inc_ref(v_options_5929_);
    lean_inc_ref(v_lctx_5928_);
    v___x_5930_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5930_, 0, v_env_5925_);
    lean_ctor_set(v___x_5930_, 1, v_mctx_5927_);
    lean_ctor_set(v___x_5930_, 2, v_lctx_5928_);
    lean_ctor_set(v___x_5930_, 3, v_options_5929_);
    v___x_5931_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5931_, 0, v___x_5930_);
    lean_ctor_set(v___x_5931_, 1, v_msgData_5918_);
    v___x_5932_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5932_, 0, v___x_5931_);
    return v___x_5932_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(
    mut v_msgData_5933_: *mut LeanObject,
    mut v___y_5934_: *mut LeanObject,
    mut v___y_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5939_: *mut LeanObject = core::ptr::null_mut();
    v_res_5939_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_);
    lean_dec(v___y_5937_);
    lean_dec_ref(v___y_5936_);
    lean_dec(v___y_5935_);
    lean_dec_ref(v___y_5934_);
    return v_res_5939_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
    mut v_msg_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
    mut v___y_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5951_: u8 = 0;
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5946_ = lean_ctor_get(v___y_5943_, 5);
                v___x_5947_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
                v_a_5948_ = lean_ctor_get(v___x_5947_, 0);
                v_isSharedCheck_5956_ = (!lean_is_exclusive(v___x_5947_)) as u8;
                if v_isSharedCheck_5956_ == 0 {
                    v___x_5950_ = v___x_5947_;
                    v_isShared_5951_ = v_isSharedCheck_5956_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5948_);
                    lean_dec(v___x_5947_);
                    v___x_5950_ = lean_box(0);
                    v_isShared_5951_ = v_isSharedCheck_5956_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5946_);
                v___x_5952_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5952_, 0, v_ref_5946_);
                lean_ctor_set(v___x_5952_, 1, v_a_5948_);
                if v_isShared_5951_ == 0 {
                    lean_ctor_set_tag(v___x_5950_, 1);
                    lean_ctor_set(v___x_5950_, 0, v___x_5952_);
                    v___x_5954_ = v___x_5950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5955_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5955_, 0, v___x_5952_);
                    v___x_5954_ = v_reuseFailAlloc_5955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(
    mut v_msg_5957_: *mut LeanObject,
    mut v___y_5958_: *mut LeanObject,
    mut v___y_5959_: *mut LeanObject,
    mut v___y_5960_: *mut LeanObject,
    mut v___y_5961_: *mut LeanObject,
    mut v___y_5962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5963_: *mut LeanObject = core::ptr::null_mut();
    v_res_5963_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
        v_msg_5957_,
        v___y_5958_,
        v___y_5959_,
        v___y_5960_,
        v___y_5961_,
    );
    lean_dec(v___y_5961_);
    lean_dec_ref(v___y_5960_);
    lean_dec(v___y_5959_);
    lean_dec_ref(v___y_5958_);
    return v_res_5963_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(
    mut v_sz_5964_: usize,
    mut v_i_5965_: usize,
    mut v_bs_5966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5967_: u8 = 0;
    let mut v_v_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: usize = 0;
    let mut v___x_5973_: usize = 0;
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5967_ = lean_usize_dec_lt(v_i_5965_, v_sz_5964_);
                if v___x_5967_ == 0 {
                    return v_bs_5966_;
                } else {
                    v_v_5968_ = lean_array_uget(v_bs_5966_, v_i_5965_);
                    v___x_5969_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5970_ = lean_array_uset(v_bs_5966_, v_i_5965_, v___x_5969_);
                    v___x_5971_ = l_Lean_Expr_mvarId_x21(v_v_5968_);
                    lean_dec(v_v_5968_);
                    v___x_5972_ = 1usize;
                    v___x_5973_ = lean_usize_add(v_i_5965_, v___x_5972_);
                    v___x_5974_ = lean_array_uset(v_bs_x27_5970_, v_i_5965_, v___x_5971_);
                    v_i_5965_ = v___x_5973_;
                    v_bs_5966_ = v___x_5974_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(
    mut v_sz_5976_: *mut LeanObject,
    mut v_i_5977_: *mut LeanObject,
    mut v_bs_5978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5979_: usize = 0;
    let mut v_i_boxed_5980_: usize = 0;
    let mut v_res_5981_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5979_ = lean_unbox_usize(v_sz_5976_);
    lean_dec(v_sz_5976_);
    v_i_boxed_5980_ = lean_unbox_usize(v_i_5977_);
    lean_dec(v_i_5977_);
    v_res_5981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_5979_, v_i_boxed_5980_, v_bs_5978_);
    return v_res_5981_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    v___x_5983_ = l_Lean_MVarId_applyN___lam__0___closed__0;
    v___x_5984_ = l_Lean_stringToMessageData(v___x_5983_);
    return v___x_5984_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    v___x_5986_ = l_Lean_MVarId_applyN___lam__0___closed__2;
    v___x_5987_ = l_Lean_stringToMessageData(v___x_5986_);
    return v___x_5987_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Lean_MVarId_applyN___lam__0___closed__4;
    v___x_5990_ = l_Lean_stringToMessageData(v___x_5989_);
    return v___x_5990_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    v___x_5992_ = l_Lean_MVarId_applyN___lam__0___closed__6;
    v___x_5993_ = l_Lean_stringToMessageData(v___x_5992_);
    return v___x_5993_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__9() -> *mut LeanObject {
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    v___x_5995_ = l_Lean_MVarId_applyN___lam__0___closed__8;
    v___x_5996_ = l_Lean_stringToMessageData(v___x_5995_);
    return v___x_5996_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    v___x_5998_ = l_Lean_MVarId_applyN___lam__0___closed__10;
    v___x_5999_ = l_Lean_stringToMessageData(v___x_5998_);
    return v___x_5999_;
}
pub unsafe fn l_Lean_MVarId_applyN___lam__0(
    mut v_mvarId_6000_: *mut LeanObject,
    mut v___x_6001_: *mut LeanObject,
    mut v_e_6002_: *mut LeanObject,
    mut v_n_6003_: *mut LeanObject,
    mut v_useApproxDefEq_6004_: u8,
    mut v___y_6005_: *mut LeanObject,
    mut v___y_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
    mut v___y_6008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6022_: u8 = 0;
    let mut v___y_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6029_: u8 = 0;
    let mut v_sz_6030_: usize = 0;
    let mut v___x_6031_: usize = 0;
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v_unused_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___y_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6072_: u8 = 0;
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6076_: u8 = 0;
    let mut v_reuseFailAlloc_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6102_: u8 = 0;
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6106_: u8 = 0;
    let mut v_isSharedCheck_6107_: u8 = 0;
    let mut v_unused_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v_a_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6113_: u8 = 0;
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_a_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_a_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6129_: u8 = 0;
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6133_: u8 = 0;
    let mut v_a_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6137_: u8 = 0;
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_6000_);
                v___x_6010_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6000_,
                    v___x_6001_,
                    v___y_6005_,
                    v___y_6006_,
                    v___y_6007_,
                    v___y_6008_,
                );
                if lean_obj_tag(v___x_6010_) == 0 {
                    lean_dec_ref_known(v___x_6010_, 1);
                    lean_inc(v_mvarId_6000_);
                    v___x_6011_ = l_Lean_MVarId_getType(
                        v_mvarId_6000_,
                        v___y_6005_,
                        v___y_6006_,
                        v___y_6007_,
                        v___y_6008_,
                    );
                    if lean_obj_tag(v___x_6011_) == 0 {
                        v_a_6012_ = lean_ctor_get(v___x_6011_, 0);
                        lean_inc(v_a_6012_);
                        lean_dec_ref_known(v___x_6011_, 1);
                        lean_inc(v___y_6008_);
                        lean_inc_ref(v___y_6007_);
                        lean_inc(v___y_6006_);
                        lean_inc_ref(v___y_6005_);
                        lean_inc_ref(v_e_6002_);
                        v___x_6013_ = lean_infer_type(
                            v_e_6002_,
                            v___y_6005_,
                            v___y_6006_,
                            v___y_6007_,
                            v___y_6008_,
                        );
                        if lean_obj_tag(v___x_6013_) == 0 {
                            v_a_6014_ = lean_ctor_get(v___x_6013_, 0);
                            lean_inc(v_a_6014_);
                            lean_dec_ref_known(v___x_6013_, 1);
                            v___x_6015_ = 0;
                            lean_inc(v_n_6003_);
                            v___x_6016_ = l_Lean_Meta_forallMetaBoundedTelescope(
                                v_a_6014_,
                                v_n_6003_,
                                v___x_6015_,
                                v___y_6005_,
                                v___y_6006_,
                                v___y_6007_,
                                v___y_6008_,
                            );
                            if lean_obj_tag(v___x_6016_) == 0 {
                                v_a_6017_ = lean_ctor_get(v___x_6016_, 0);
                                lean_inc(v_a_6017_);
                                lean_dec_ref_known(v___x_6016_, 1);
                                v_fst_6018_ = lean_ctor_get(v_a_6017_, 0);
                                v_snd_6019_ = lean_ctor_get(v_a_6017_, 1);
                                v_isSharedCheck_6109_ = (!lean_is_exclusive(v_a_6017_)) as u8;
                                if v_isSharedCheck_6109_ == 0 {
                                    v___x_6021_ = v_a_6017_;
                                    v_isShared_6022_ = v_isSharedCheck_6109_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_6019_);
                                    lean_inc(v_fst_6018_);
                                    lean_dec(v_a_6017_);
                                    v___x_6021_ = lean_box(0);
                                    v_isShared_6022_ = v_isSharedCheck_6109_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6012_);
                                lean_dec(v___y_6008_);
                                lean_dec_ref(v___y_6007_);
                                lean_dec(v___y_6006_);
                                lean_dec_ref(v___y_6005_);
                                lean_dec(v_n_6003_);
                                lean_dec_ref(v_e_6002_);
                                lean_dec(v_mvarId_6000_);
                                v_a_6110_ = lean_ctor_get(v___x_6016_, 0);
                                v_isSharedCheck_6117_ = (!lean_is_exclusive(v___x_6016_)) as u8;
                                if v_isSharedCheck_6117_ == 0 {
                                    v___x_6112_ = v___x_6016_;
                                    v_isShared_6113_ = v_isSharedCheck_6117_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_6110_);
                                    lean_dec(v___x_6016_);
                                    v___x_6112_ = lean_box(0);
                                    v_isShared_6113_ = v_isSharedCheck_6117_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6012_);
                            lean_dec(v___y_6008_);
                            lean_dec_ref(v___y_6007_);
                            lean_dec(v___y_6006_);
                            lean_dec_ref(v___y_6005_);
                            lean_dec(v_n_6003_);
                            lean_dec_ref(v_e_6002_);
                            lean_dec(v_mvarId_6000_);
                            v_a_6118_ = lean_ctor_get(v___x_6013_, 0);
                            v_isSharedCheck_6125_ = (!lean_is_exclusive(v___x_6013_)) as u8;
                            if v_isSharedCheck_6125_ == 0 {
                                v___x_6120_ = v___x_6013_;
                                v_isShared_6121_ = v_isSharedCheck_6125_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_6118_);
                                lean_dec(v___x_6013_);
                                v___x_6120_ = lean_box(0);
                                v_isShared_6121_ = v_isSharedCheck_6125_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_6008_);
                        lean_dec_ref(v___y_6007_);
                        lean_dec(v___y_6006_);
                        lean_dec_ref(v___y_6005_);
                        lean_dec(v_n_6003_);
                        lean_dec_ref(v_e_6002_);
                        lean_dec(v_mvarId_6000_);
                        v_a_6126_ = lean_ctor_get(v___x_6011_, 0);
                        v_isSharedCheck_6133_ = (!lean_is_exclusive(v___x_6011_)) as u8;
                        if v_isSharedCheck_6133_ == 0 {
                            v___x_6128_ = v___x_6011_;
                            v_isShared_6129_ = v_isSharedCheck_6133_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_6126_);
                            lean_dec(v___x_6011_);
                            v___x_6128_ = lean_box(0);
                            v_isShared_6129_ = v_isSharedCheck_6133_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_6008_);
                    lean_dec_ref(v___y_6007_);
                    lean_dec(v___y_6006_);
                    lean_dec_ref(v___y_6005_);
                    lean_dec(v_n_6003_);
                    lean_dec_ref(v_e_6002_);
                    lean_dec(v_mvarId_6000_);
                    v_a_6134_ = lean_ctor_get(v___x_6010_, 0);
                    v_isSharedCheck_6141_ = (!lean_is_exclusive(v___x_6010_)) as u8;
                    if v_isSharedCheck_6141_ == 0 {
                        v___x_6136_ = v___x_6010_;
                        v_isShared_6137_ = v_isSharedCheck_6141_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_6134_);
                        lean_dec(v___x_6010_);
                        v___x_6136_ = lean_box(0);
                        v_isShared_6137_ = v_isSharedCheck_6141_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6039_ = lean_ctor_get(v_snd_6019_, 1);
                v_isSharedCheck_6107_ = (!lean_is_exclusive(v_snd_6019_)) as u8;
                if v_isSharedCheck_6107_ == 0 {
                    v_unused_6108_ = lean_ctor_get(v_snd_6019_, 0);
                    lean_dec(v_unused_6108_);
                    v___x_6041_ = v_snd_6019_;
                    v_isShared_6042_ = v_isSharedCheck_6107_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_6039_);
                    lean_dec(v_snd_6019_);
                    v___x_6041_ = lean_box(0);
                    v_isShared_6042_ = v_isSharedCheck_6107_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                lean_inc(v_fst_6018_);
                v___x_6025_ = l_Lean_Expr_beta(v_e_6002_, v_fst_6018_);
                v___x_6026_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                    v_mvarId_6000_,
                    v___x_6025_,
                    v___y_6024_,
                );
                lean_dec(v___y_6024_);
                v_isSharedCheck_6037_ = (!lean_is_exclusive(v___x_6026_)) as u8;
                if v_isSharedCheck_6037_ == 0 {
                    v_unused_6038_ = lean_ctor_get(v___x_6026_, 0);
                    lean_dec(v_unused_6038_);
                    v___x_6028_ = v___x_6026_;
                    v_isShared_6029_ = v_isSharedCheck_6037_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_6026_);
                    v___x_6028_ = lean_box(0);
                    v_isShared_6029_ = v_isSharedCheck_6037_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_6030_ = lean_array_size(v_fst_6018_);
                v___x_6031_ = 0usize;
                v___x_6032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_6030_, v___x_6031_, v_fst_6018_);
                v___x_6033_ = lean_array_to_list(v___x_6032_);
                if v_isShared_6029_ == 0 {
                    lean_ctor_set(v___x_6028_, 0, v___x_6033_);
                    v___x_6035_ = v___x_6028_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_6033_);
                    v___x_6035_ = v_reuseFailAlloc_6036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6035_;
            }
            5 => {
                v___x_6087_ = lean_array_get_size(v_fst_6018_);
                v___x_6088_ = lean_nat_dec_eq(v___x_6087_, v_n_6003_);
                if v___x_6088_ == 0 {
                    lean_del_object(v___x_6041_);
                    lean_del_object(v___x_6021_);
                    lean_dec(v_fst_6018_);
                    lean_dec(v_a_6012_);
                    lean_dec_ref(v_e_6002_);
                    lean_dec(v_mvarId_6000_);
                    v___x_6089_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__9_once),
                        _init_l_Lean_MVarId_applyN___lam__0___closed__9,
                    );
                    v___x_6090_ = l_Nat_reprFast(v_n_6003_);
                    v___x_6091_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_6091_, 0, v___x_6090_);
                    v___x_6092_ = l_Lean_MessageData_ofFormat(v___x_6091_);
                    v___x_6093_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6093_, 0, v___x_6089_);
                    lean_ctor_set(v___x_6093_, 1, v___x_6092_);
                    v___x_6094_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__11),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__11_once),
                        _init_l_Lean_MVarId_applyN___lam__0___closed__11,
                    );
                    v___x_6095_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6095_, 0, v___x_6093_);
                    lean_ctor_set(v___x_6095_, 1, v___x_6094_);
                    v___x_6096_ = l_Lean_indentExpr(v_snd_6039_);
                    v___x_6097_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6097_, 0, v___x_6095_);
                    lean_ctor_set(v___x_6097_, 1, v___x_6096_);
                    v___x_6098_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                        v___x_6097_,
                        v___y_6005_,
                        v___y_6006_,
                        v___y_6007_,
                        v___y_6008_,
                    );
                    lean_dec(v___y_6008_);
                    lean_dec_ref(v___y_6007_);
                    lean_dec(v___y_6006_);
                    lean_dec_ref(v___y_6005_);
                    v_a_6099_ = lean_ctor_get(v___x_6098_, 0);
                    v_isSharedCheck_6106_ = (!lean_is_exclusive(v___x_6098_)) as u8;
                    if v_isSharedCheck_6106_ == 0 {
                        v___x_6101_ = v___x_6098_;
                        v_isShared_6102_ = v_isSharedCheck_6106_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_6099_);
                        lean_dec(v___x_6098_);
                        v___x_6101_ = lean_box(0);
                        v_isShared_6102_ = v_isSharedCheck_6106_;
                        state = 13;
                        continue;
                    }
                } else {
                    v___y_6044_ = v___y_6005_;
                    v___y_6045_ = v___y_6006_;
                    v___y_6046_ = v___y_6007_;
                    v___y_6047_ = v___y_6008_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc(v_a_6012_);
                lean_inc(v_snd_6039_);
                v___x_6048_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
                    v_useApproxDefEq_6004_,
                    v_snd_6039_,
                    v_a_6012_,
                    v___y_6044_,
                    v___y_6045_,
                    v___y_6046_,
                    v___y_6047_,
                );
                if lean_obj_tag(v___x_6048_) == 0 {
                    v_a_6049_ = lean_ctor_get(v___x_6048_, 0);
                    lean_inc(v_a_6049_);
                    lean_dec_ref_known(v___x_6048_, 1);
                    v___x_6050_ = (lean_unbox(v_a_6049_) as u8);
                    lean_dec(v_a_6049_);
                    if v___x_6050_ == 0 {
                        lean_dec(v_fst_6018_);
                        lean_dec_ref(v_e_6002_);
                        lean_dec(v_mvarId_6000_);
                        v___x_6051_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__1_once),
                            _init_l_Lean_MVarId_applyN___lam__0___closed__1,
                        );
                        v___x_6052_ = l_Lean_indentExpr(v_a_6012_);
                        if v_isShared_6042_ == 0 {
                            lean_ctor_set_tag(v___x_6041_, 7);
                            lean_ctor_set(v___x_6041_, 1, v___x_6052_);
                            lean_ctor_set(v___x_6041_, 0, v___x_6051_);
                            v___x_6054_ = v___x_6041_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6078_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6051_);
                            lean_ctor_set(v_reuseFailAlloc_6078_, 1, v___x_6052_);
                            v___x_6054_ = v_reuseFailAlloc_6078_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_6047_);
                        lean_dec_ref(v___y_6046_);
                        lean_dec_ref(v___y_6044_);
                        lean_del_object(v___x_6041_);
                        lean_dec(v_snd_6039_);
                        lean_del_object(v___x_6021_);
                        lean_dec(v_a_6012_);
                        lean_dec(v_n_6003_);
                        v___y_6024_ = v___y_6045_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_6047_);
                    lean_dec_ref(v___y_6046_);
                    lean_dec(v___y_6045_);
                    lean_dec_ref(v___y_6044_);
                    lean_del_object(v___x_6041_);
                    lean_dec(v_snd_6039_);
                    lean_del_object(v___x_6021_);
                    lean_dec(v_fst_6018_);
                    lean_dec(v_a_6012_);
                    lean_dec(v_n_6003_);
                    lean_dec_ref(v_e_6002_);
                    lean_dec(v_mvarId_6000_);
                    v_a_6079_ = lean_ctor_get(v___x_6048_, 0);
                    v_isSharedCheck_6086_ = (!lean_is_exclusive(v___x_6048_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6081_ = v___x_6048_;
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6079_);
                        lean_dec(v___x_6048_);
                        v___x_6081_ = lean_box(0);
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6055_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_applyN___lam__0___closed__3,
                );
                if v_isShared_6022_ == 0 {
                    lean_ctor_set_tag(v___x_6021_, 7);
                    lean_ctor_set(v___x_6021_, 1, v___x_6055_);
                    lean_ctor_set(v___x_6021_, 0, v___x_6054_);
                    v___x_6057_ = v___x_6021_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6077_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6054_);
                    lean_ctor_set(v_reuseFailAlloc_6077_, 1, v___x_6055_);
                    v___x_6057_ = v_reuseFailAlloc_6077_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6058_ = l_Lean_indentExpr(v_snd_6039_);
                v___x_6059_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6059_, 0, v___x_6057_);
                lean_ctor_set(v___x_6059_, 1, v___x_6058_);
                v___x_6060_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__5_once),
                    _init_l_Lean_MVarId_applyN___lam__0___closed__5,
                );
                v___x_6061_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6061_, 0, v___x_6059_);
                lean_ctor_set(v___x_6061_, 1, v___x_6060_);
                v___x_6062_ = l_Nat_reprFast(v_n_6003_);
                v___x_6063_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6063_, 0, v___x_6062_);
                v___x_6064_ = l_Lean_MessageData_ofFormat(v___x_6063_);
                v___x_6065_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6065_, 0, v___x_6061_);
                lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                v___x_6066_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__7_once),
                    _init_l_Lean_MVarId_applyN___lam__0___closed__7,
                );
                v___x_6067_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6067_, 0, v___x_6065_);
                lean_ctor_set(v___x_6067_, 1, v___x_6066_);
                v___x_6068_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                    v___x_6067_,
                    v___y_6044_,
                    v___y_6045_,
                    v___y_6046_,
                    v___y_6047_,
                );
                lean_dec(v___y_6047_);
                lean_dec_ref(v___y_6046_);
                lean_dec(v___y_6045_);
                lean_dec_ref(v___y_6044_);
                v_a_6069_ = lean_ctor_get(v___x_6068_, 0);
                v_isSharedCheck_6076_ = (!lean_is_exclusive(v___x_6068_)) as u8;
                if v_isSharedCheck_6076_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    v_isShared_6072_ = v_isSharedCheck_6076_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_a_6069_);
                    lean_dec(v___x_6068_);
                    v___x_6071_ = lean_box(0);
                    v_isShared_6072_ = v_isSharedCheck_6076_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6072_ == 0 {
                    v___x_6074_ = v___x_6071_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_a_6069_);
                    v___x_6074_ = v_reuseFailAlloc_6075_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6074_;
            }
            11 => {
                if v_isShared_6082_ == 0 {
                    v___x_6084_ = v___x_6081_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
                    v___x_6084_ = v_reuseFailAlloc_6085_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6084_;
            }
            13 => {
                if v_isShared_6102_ == 0 {
                    v___x_6104_ = v___x_6101_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
                    v___x_6104_ = v_reuseFailAlloc_6105_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6104_;
            }
            15 => {
                if v_isShared_6113_ == 0 {
                    v___x_6115_ = v___x_6112_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6110_);
                    v___x_6115_ = v_reuseFailAlloc_6116_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6115_;
            }
            17 => {
                if v_isShared_6121_ == 0 {
                    v___x_6123_ = v___x_6120_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6118_);
                    v___x_6123_ = v_reuseFailAlloc_6124_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6123_;
            }
            19 => {
                if v_isShared_6129_ == 0 {
                    v___x_6131_ = v___x_6128_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_a_6126_);
                    v___x_6131_ = v_reuseFailAlloc_6132_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6131_;
            }
            21 => {
                if v_isShared_6137_ == 0 {
                    v___x_6139_ = v___x_6136_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_a_6134_);
                    v___x_6139_ = v_reuseFailAlloc_6140_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyN___lam__0___boxed(
    mut v_mvarId_6142_: *mut LeanObject,
    mut v___x_6143_: *mut LeanObject,
    mut v_e_6144_: *mut LeanObject,
    mut v_n_6145_: *mut LeanObject,
    mut v_useApproxDefEq_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useApproxDefEq_boxed_6152_: u8 = 0;
    let mut v_res_6153_: *mut LeanObject = core::ptr::null_mut();
    v_useApproxDefEq_boxed_6152_ = (lean_unbox(v_useApproxDefEq_6146_) as u8);
    v_res_6153_ = l_Lean_MVarId_applyN___lam__0(
        v_mvarId_6142_,
        v___x_6143_,
        v_e_6144_,
        v_n_6145_,
        v_useApproxDefEq_boxed_6152_,
        v___y_6147_,
        v___y_6148_,
        v___y_6149_,
        v___y_6150_,
    );
    return v_res_6153_;
}
pub unsafe fn l_Lean_MVarId_applyN(
    mut v_mvarId_6154_: *mut LeanObject,
    mut v_e_6155_: *mut LeanObject,
    mut v_n_6156_: *mut LeanObject,
    mut v_useApproxDefEq_6157_: u8,
    mut v_a_6158_: *mut LeanObject,
    mut v_a_6159_: *mut LeanObject,
    mut v_a_6160_: *mut LeanObject,
    mut v_a_6161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    v___x_6163_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
    v___x_6164_ = lean_box((v_useApproxDefEq_6157_) as usize);
    lean_inc(v_mvarId_6154_);
    v___f_6165_ = lean_alloc_closure(
        l_Lean_MVarId_applyN___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_6165_, 0, v_mvarId_6154_);
    lean_closure_set(v___f_6165_, 1, v___x_6163_);
    lean_closure_set(v___f_6165_, 2, v_e_6155_);
    lean_closure_set(v___f_6165_, 3, v_n_6156_);
    lean_closure_set(v___f_6165_, 4, v___x_6164_);
    v___x_6166_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_6154_,
        v___f_6165_,
        v_a_6158_,
        v_a_6159_,
        v_a_6160_,
        v_a_6161_,
    );
    return v___x_6166_;
}
pub unsafe fn l_Lean_MVarId_applyN___boxed(
    mut v_mvarId_6167_: *mut LeanObject,
    mut v_e_6168_: *mut LeanObject,
    mut v_n_6169_: *mut LeanObject,
    mut v_useApproxDefEq_6170_: *mut LeanObject,
    mut v_a_6171_: *mut LeanObject,
    mut v_a_6172_: *mut LeanObject,
    mut v_a_6173_: *mut LeanObject,
    mut v_a_6174_: *mut LeanObject,
    mut v_a_6175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useApproxDefEq_boxed_6176_: u8 = 0;
    let mut v_res_6177_: *mut LeanObject = core::ptr::null_mut();
    v_useApproxDefEq_boxed_6176_ = (lean_unbox(v_useApproxDefEq_6170_) as u8);
    v_res_6177_ = l_Lean_MVarId_applyN(
        v_mvarId_6167_,
        v_e_6168_,
        v_n_6169_,
        v_useApproxDefEq_boxed_6176_,
        v_a_6171_,
        v_a_6172_,
        v_a_6173_,
        v_a_6174_,
    );
    lean_dec(v_a_6174_);
    lean_dec_ref(v_a_6173_);
    lean_dec(v_a_6172_);
    lean_dec_ref(v_a_6171_);
    return v_res_6177_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(
    mut v_00_u03b1_6178_: *mut LeanObject,
    mut v_msg_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
    mut v___y_6182_: *mut LeanObject,
    mut v___y_6183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    v___x_6185_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
        v_msg_6179_,
        v___y_6180_,
        v___y_6181_,
        v___y_6182_,
        v___y_6183_,
    );
    return v___x_6185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(
    mut v_00_u03b1_6186_: *mut LeanObject,
    mut v_msg_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6193_: *mut LeanObject = core::ptr::null_mut();
    v_res_6193_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(
        v_00_u03b1_6186_,
        v_msg_6187_,
        v___y_6188_,
        v___y_6189_,
        v___y_6190_,
        v___y_6191_,
    );
    lean_dec(v___y_6191_);
    lean_dec_ref(v___y_6190_);
    lean_dec(v___y_6189_);
    lean_dec_ref(v___y_6188_);
    return v_res_6193_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6()
-> *mut LeanObject {
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    v___x_6204_ = lean_box(0);
    v___x_6205_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5;
    v___x_6206_ = l_Lean_mkConst(v___x_6205_, v___x_6204_);
    return v___x_6206_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
    mut v_tag_6207_: *mut LeanObject,
    mut v_type_6208_: *mut LeanObject,
    mut v_a_6209_: *mut LeanObject,
    mut v_a_6210_: *mut LeanObject,
    mut v_a_6211_: *mut LeanObject,
    mut v_a_6212_: *mut LeanObject,
    mut v_a_6213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6231_: u8 = 0;
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6249_: u8 = 0;
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_6213_);
                lean_inc_ref(v_a_6212_);
                lean_inc(v_a_6211_);
                lean_inc_ref(v_a_6210_);
                v___x_6215_ = lean_whnf(v_type_6208_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                if lean_obj_tag(v___x_6215_) == 0 {
                    v_a_6216_ = lean_ctor_get(v___x_6215_, 0);
                    lean_inc(v_a_6216_);
                    lean_dec_ref_known(v___x_6215_, 1);
                    v___x_6217_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1;
                    v___x_6218_ = lean_unsigned_to_nat(2);
                    v___x_6219_ = l_Lean_Expr_isAppOfArity(v_a_6216_, v___x_6217_, v___x_6218_);
                    if v___x_6219_ == 0 {
                        v___x_6220_ = lean_st_ref_get(v_a_6209_);
                        v___x_6221_ = lean_array_get_size(v___x_6220_);
                        lean_dec(v___x_6220_);
                        v___x_6222_ = lean_unsigned_to_nat(1);
                        v___x_6223_ = lean_nat_add(v___x_6221_, v___x_6222_);
                        v___x_6224_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3;
                        v___x_6225_ = lean_name_append_index_after(v___x_6224_, v___x_6223_);
                        v___x_6226_ = l_Lean_Name_append(v_tag_6207_, v___x_6225_);
                        v___x_6227_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v_a_6216_,
                            v___x_6226_,
                            v_a_6210_,
                            v_a_6211_,
                            v_a_6212_,
                            v_a_6213_,
                        );
                        if lean_obj_tag(v___x_6227_) == 0 {
                            v_a_6228_ = lean_ctor_get(v___x_6227_, 0);
                            v_isSharedCheck_6239_ = (!lean_is_exclusive(v___x_6227_)) as u8;
                            if v_isSharedCheck_6239_ == 0 {
                                v___x_6230_ = v___x_6227_;
                                v_isShared_6231_ = v_isSharedCheck_6239_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6228_);
                                lean_dec(v___x_6227_);
                                v___x_6230_ = lean_box(0);
                                v_isShared_6231_ = v_isSharedCheck_6239_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_6227_;
                        }
                    } else {
                        v___x_6240_ = l_Lean_Expr_appFn_x21(v_a_6216_);
                        v___x_6241_ = l_Lean_Expr_appArg_x21(v___x_6240_);
                        lean_dec_ref(v___x_6240_);
                        lean_inc_ref(v___x_6241_);
                        lean_inc(v_tag_6207_);
                        v___x_6242_ =
                            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
                                v_tag_6207_,
                                v___x_6241_,
                                v_a_6209_,
                                v_a_6210_,
                                v_a_6211_,
                                v_a_6212_,
                                v_a_6213_,
                            );
                        if lean_obj_tag(v___x_6242_) == 0 {
                            v_a_6243_ = lean_ctor_get(v___x_6242_, 0);
                            lean_inc(v_a_6243_);
                            lean_dec_ref_known(v___x_6242_, 1);
                            v___x_6244_ = l_Lean_Expr_appArg_x21(v_a_6216_);
                            lean_dec(v_a_6216_);
                            lean_inc_ref(v___x_6244_);
                            v___x_6245_ =
                                l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
                                    v_tag_6207_,
                                    v___x_6244_,
                                    v_a_6209_,
                                    v_a_6210_,
                                    v_a_6211_,
                                    v_a_6212_,
                                    v_a_6213_,
                                );
                            if lean_obj_tag(v___x_6245_) == 0 {
                                v_a_6246_ = lean_ctor_get(v___x_6245_, 0);
                                v_isSharedCheck_6255_ = (!lean_is_exclusive(v___x_6245_)) as u8;
                                if v_isSharedCheck_6255_ == 0 {
                                    v___x_6248_ = v___x_6245_;
                                    v_isShared_6249_ = v_isSharedCheck_6255_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6246_);
                                    lean_dec(v___x_6245_);
                                    v___x_6248_ = lean_box(0);
                                    v_isShared_6249_ = v_isSharedCheck_6255_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_6244_);
                                lean_dec(v_a_6243_);
                                lean_dec_ref(v___x_6241_);
                                return v___x_6245_;
                            }
                        } else {
                            lean_dec_ref(v___x_6241_);
                            lean_dec(v_a_6216_);
                            lean_dec(v_tag_6207_);
                            return v___x_6242_;
                        }
                    }
                } else {
                    lean_dec(v_tag_6207_);
                    return v___x_6215_;
                }
            }
            1 => {
                v___x_6232_ = lean_st_ref_take(v_a_6209_);
                v___x_6233_ = l_Lean_Expr_mvarId_x21(v_a_6228_);
                v___x_6234_ = lean_array_push(v___x_6232_, v___x_6233_);
                v___x_6235_ = lean_st_ref_set(v_a_6209_, v___x_6234_);
                if v_isShared_6231_ == 0 {
                    v___x_6237_ = v___x_6230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6228_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6237_;
            }
            3 => {
                v___x_6250_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
                v___x_6251_ =
                    l_Lean_mkApp4(v___x_6250_, v___x_6241_, v___x_6244_, v_a_6243_, v_a_6246_);
                if v_isShared_6249_ == 0 {
                    lean_ctor_set(v___x_6248_, 0, v___x_6251_);
                    v___x_6253_ = v___x_6248_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6254_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6254_, 0, v___x_6251_);
                    v___x_6253_ = v_reuseFailAlloc_6254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(
    mut v_tag_6256_: *mut LeanObject,
    mut v_type_6257_: *mut LeanObject,
    mut v_a_6258_: *mut LeanObject,
    mut v_a_6259_: *mut LeanObject,
    mut v_a_6260_: *mut LeanObject,
    mut v_a_6261_: *mut LeanObject,
    mut v_a_6262_: *mut LeanObject,
    mut v_a_6263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6264_: *mut LeanObject = core::ptr::null_mut();
    v_res_6264_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
        v_tag_6256_,
        v_type_6257_,
        v_a_6258_,
        v_a_6259_,
        v_a_6260_,
        v_a_6261_,
        v_a_6262_,
    );
    lean_dec(v_a_6262_);
    lean_dec_ref(v_a_6261_);
    lean_dec(v_a_6260_);
    lean_dec_ref(v_a_6259_);
    lean_dec(v_a_6258_);
    return v_res_6264_;
}
pub unsafe fn l_Lean_MVarId_splitAndCore___lam__0(
    mut v_mvarId_6265_: *mut LeanObject,
    mut v___x_6266_: *mut LeanObject,
    mut v___y_6267_: *mut LeanObject,
    mut v___y_6268_: *mut LeanObject,
    mut v___y_6269_: *mut LeanObject,
    mut v___y_6270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6277_: u8 = 0;
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: u8 = 0;
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6296_: u8 = 0;
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_unused_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_a_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6318_: u8 = 0;
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut v_a_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6323_: u8 = 0;
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6327_: u8 = 0;
    let mut v_a_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6331_: u8 = 0;
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_6265_);
                v___x_6272_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6265_,
                    v___x_6266_,
                    v___y_6267_,
                    v___y_6268_,
                    v___y_6269_,
                    v___y_6270_,
                );
                if lean_obj_tag(v___x_6272_) == 0 {
                    lean_dec_ref_known(v___x_6272_, 1);
                    lean_inc(v_mvarId_6265_);
                    v___x_6273_ = l_Lean_MVarId_getType_x27(
                        v_mvarId_6265_,
                        v___y_6267_,
                        v___y_6268_,
                        v___y_6269_,
                        v___y_6270_,
                    );
                    if lean_obj_tag(v___x_6273_) == 0 {
                        v_a_6274_ = lean_ctor_get(v___x_6273_, 0);
                        v_isSharedCheck_6319_ = (!lean_is_exclusive(v___x_6273_)) as u8;
                        if v_isSharedCheck_6319_ == 0 {
                            v___x_6276_ = v___x_6273_;
                            v_isShared_6277_ = v_isSharedCheck_6319_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6274_);
                            lean_dec(v___x_6273_);
                            v___x_6276_ = lean_box(0);
                            v_isShared_6277_ = v_isSharedCheck_6319_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_mvarId_6265_);
                        v_a_6320_ = lean_ctor_get(v___x_6273_, 0);
                        v_isSharedCheck_6327_ = (!lean_is_exclusive(v___x_6273_)) as u8;
                        if v_isSharedCheck_6327_ == 0 {
                            v___x_6322_ = v___x_6273_;
                            v_isShared_6323_ = v_isSharedCheck_6327_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6320_);
                            lean_dec(v___x_6273_);
                            v___x_6322_ = lean_box(0);
                            v_isShared_6323_ = v_isSharedCheck_6327_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_6265_);
                    v_a_6328_ = lean_ctor_get(v___x_6272_, 0);
                    v_isSharedCheck_6335_ = (!lean_is_exclusive(v___x_6272_)) as u8;
                    if v_isSharedCheck_6335_ == 0 {
                        v___x_6330_ = v___x_6272_;
                        v_isShared_6331_ = v_isSharedCheck_6335_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6328_);
                        lean_dec(v___x_6272_);
                        v___x_6330_ = lean_box(0);
                        v_isShared_6331_ = v_isSharedCheck_6335_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6278_ =
                    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1;
                v___x_6279_ = lean_unsigned_to_nat(2);
                v___x_6280_ = l_Lean_Expr_isAppOfArity(v_a_6274_, v___x_6278_, v___x_6279_);
                if v___x_6280_ == 0 {
                    lean_dec(v_a_6274_);
                    v___x_6281_ = lean_box(0);
                    v___x_6282_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6282_, 0, v_mvarId_6265_);
                    lean_ctor_set(v___x_6282_, 1, v___x_6281_);
                    if v_isShared_6277_ == 0 {
                        lean_ctor_set(v___x_6276_, 0, v___x_6282_);
                        v___x_6284_ = v___x_6276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6285_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6285_, 0, v___x_6282_);
                        v___x_6284_ = v_reuseFailAlloc_6285_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6276_);
                    lean_inc(v_mvarId_6265_);
                    v___x_6286_ = l_Lean_MVarId_getTag(
                        v_mvarId_6265_,
                        v___y_6267_,
                        v___y_6268_,
                        v___y_6269_,
                        v___y_6270_,
                    );
                    if lean_obj_tag(v___x_6286_) == 0 {
                        v_a_6287_ = lean_ctor_get(v___x_6286_, 0);
                        lean_inc(v_a_6287_);
                        lean_dec_ref_known(v___x_6286_, 1);
                        v___x_6288_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0;
                        v___x_6289_ = lean_st_mk_ref(v___x_6288_);
                        v___x_6290_ =
                            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
                                v_a_6287_,
                                v_a_6274_,
                                v___x_6289_,
                                v___y_6267_,
                                v___y_6268_,
                                v___y_6269_,
                                v___y_6270_,
                            );
                        if lean_obj_tag(v___x_6290_) == 0 {
                            v_a_6291_ = lean_ctor_get(v___x_6290_, 0);
                            lean_inc(v_a_6291_);
                            lean_dec_ref_known(v___x_6290_, 1);
                            v___x_6292_ = lean_st_ref_get(v___x_6289_);
                            lean_dec(v___x_6289_);
                            v___x_6293_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                    v_mvarId_6265_,
                                    v_a_6291_,
                                    v___y_6268_,
                                );
                            v_isSharedCheck_6301_ = (!lean_is_exclusive(v___x_6293_)) as u8;
                            if v_isSharedCheck_6301_ == 0 {
                                v_unused_6302_ = lean_ctor_get(v___x_6293_, 0);
                                lean_dec(v_unused_6302_);
                                v___x_6295_ = v___x_6293_;
                                v_isShared_6296_ = v_isSharedCheck_6301_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_6293_);
                                v___x_6295_ = lean_box(0);
                                v_isShared_6296_ = v_isSharedCheck_6301_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_6289_);
                            lean_dec(v_mvarId_6265_);
                            v_a_6303_ = lean_ctor_get(v___x_6290_, 0);
                            v_isSharedCheck_6310_ = (!lean_is_exclusive(v___x_6290_)) as u8;
                            if v_isSharedCheck_6310_ == 0 {
                                v___x_6305_ = v___x_6290_;
                                v_isShared_6306_ = v_isSharedCheck_6310_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6303_);
                                lean_dec(v___x_6290_);
                                v___x_6305_ = lean_box(0);
                                v_isShared_6306_ = v_isSharedCheck_6310_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6274_);
                        lean_dec(v_mvarId_6265_);
                        v_a_6311_ = lean_ctor_get(v___x_6286_, 0);
                        v_isSharedCheck_6318_ = (!lean_is_exclusive(v___x_6286_)) as u8;
                        if v_isSharedCheck_6318_ == 0 {
                            v___x_6313_ = v___x_6286_;
                            v_isShared_6314_ = v_isSharedCheck_6318_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6311_);
                            lean_dec(v___x_6286_);
                            v___x_6313_ = lean_box(0);
                            v_isShared_6314_ = v_isSharedCheck_6318_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6284_;
            }
            3 => {
                v___x_6297_ = lean_array_to_list(v___x_6292_);
                if v_isShared_6296_ == 0 {
                    lean_ctor_set(v___x_6295_, 0, v___x_6297_);
                    v___x_6299_ = v___x_6295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6300_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 0, v___x_6297_);
                    v___x_6299_ = v_reuseFailAlloc_6300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6299_;
            }
            5 => {
                if v_isShared_6306_ == 0 {
                    v___x_6308_ = v___x_6305_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6303_);
                    v___x_6308_ = v_reuseFailAlloc_6309_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6308_;
            }
            7 => {
                if v_isShared_6314_ == 0 {
                    v___x_6316_ = v___x_6313_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_a_6311_);
                    v___x_6316_ = v_reuseFailAlloc_6317_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6316_;
            }
            9 => {
                if v_isShared_6323_ == 0 {
                    v___x_6325_ = v___x_6322_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_a_6320_);
                    v___x_6325_ = v_reuseFailAlloc_6326_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6325_;
            }
            11 => {
                if v_isShared_6331_ == 0 {
                    v___x_6333_ = v___x_6330_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6334_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_a_6328_);
                    v___x_6333_ = v_reuseFailAlloc_6334_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_splitAndCore___lam__0___boxed(
    mut v_mvarId_6336_: *mut LeanObject,
    mut v___x_6337_: *mut LeanObject,
    mut v___y_6338_: *mut LeanObject,
    mut v___y_6339_: *mut LeanObject,
    mut v___y_6340_: *mut LeanObject,
    mut v___y_6341_: *mut LeanObject,
    mut v___y_6342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6343_: *mut LeanObject = core::ptr::null_mut();
    v_res_6343_ = l_Lean_MVarId_splitAndCore___lam__0(
        v_mvarId_6336_,
        v___x_6337_,
        v___y_6338_,
        v___y_6339_,
        v___y_6340_,
        v___y_6341_,
    );
    lean_dec(v___y_6341_);
    lean_dec_ref(v___y_6340_);
    lean_dec(v___y_6339_);
    lean_dec_ref(v___y_6338_);
    return v_res_6343_;
}
pub unsafe fn l_Lean_MVarId_splitAndCore(
    mut v_mvarId_6347_: *mut LeanObject,
    mut v_a_6348_: *mut LeanObject,
    mut v_a_6349_: *mut LeanObject,
    mut v_a_6350_: *mut LeanObject,
    mut v_a_6351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    v___x_6353_ = l_Lean_MVarId_splitAndCore___closed__1;
    lean_inc(v_mvarId_6347_);
    v___f_6354_ = lean_alloc_closure(
        l_Lean_MVarId_splitAndCore___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_6354_, 0, v_mvarId_6347_);
    lean_closure_set(v___f_6354_, 1, v___x_6353_);
    v___x_6355_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_6347_,
        v___f_6354_,
        v_a_6348_,
        v_a_6349_,
        v_a_6350_,
        v_a_6351_,
    );
    return v___x_6355_;
}
pub unsafe fn l_Lean_MVarId_splitAndCore___boxed(
    mut v_mvarId_6356_: *mut LeanObject,
    mut v_a_6357_: *mut LeanObject,
    mut v_a_6358_: *mut LeanObject,
    mut v_a_6359_: *mut LeanObject,
    mut v_a_6360_: *mut LeanObject,
    mut v_a_6361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6362_: *mut LeanObject = core::ptr::null_mut();
    v_res_6362_ =
        l_Lean_MVarId_splitAndCore(v_mvarId_6356_, v_a_6357_, v_a_6358_, v_a_6359_, v_a_6360_);
    lean_dec(v_a_6360_);
    lean_dec_ref(v_a_6359_);
    lean_dec(v_a_6358_);
    lean_dec_ref(v_a_6357_);
    return v_res_6362_;
}
pub unsafe fn l_Lean_MVarId_splitAnd(
    mut v_mvarId_6363_: *mut LeanObject,
    mut v_a_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
    mut v_a_6366_: *mut LeanObject,
    mut v_a_6367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    v___x_6369_ =
        l_Lean_MVarId_splitAndCore(v_mvarId_6363_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_MVarId_splitAnd___boxed(
    mut v_mvarId_6370_: *mut LeanObject,
    mut v_a_6371_: *mut LeanObject,
    mut v_a_6372_: *mut LeanObject,
    mut v_a_6373_: *mut LeanObject,
    mut v_a_6374_: *mut LeanObject,
    mut v_a_6375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6376_: *mut LeanObject = core::ptr::null_mut();
    v_res_6376_ =
        l_Lean_MVarId_splitAnd(v_mvarId_6370_, v_a_6371_, v_a_6372_, v_a_6373_, v_a_6374_);
    lean_dec(v_a_6374_);
    lean_dec_ref(v_a_6373_);
    lean_dec(v_a_6372_);
    lean_dec_ref(v_a_6371_);
    return v_res_6376_;
}
pub unsafe fn _init_l_Lean_MVarId_exfalso___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    v___x_6380_ = lean_box(0);
    v___x_6381_ = l_Lean_MVarId_exfalso___lam__0___closed__1;
    v___x_6382_ = l_Lean_mkConst(v___x_6381_, v___x_6380_);
    return v___x_6382_;
}
pub unsafe fn l_Lean_MVarId_exfalso___lam__0(
    mut v_mvarId_6387_: *mut LeanObject,
    mut v___x_6388_: *mut LeanObject,
    mut v___y_6389_: *mut LeanObject,
    mut v___y_6390_: *mut LeanObject,
    mut v___y_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6419_: u8 = 0;
    let mut v_unused_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6424_: u8 = 0;
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6428_: u8 = 0;
    let mut v_a_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6432_: u8 = 0;
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6436_: u8 = 0;
    let mut v_a_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6440_: u8 = 0;
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6444_: u8 = 0;
    let mut v_a_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6448_: u8 = 0;
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6452_: u8 = 0;
    let mut v_a_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_6387_);
                v___x_6394_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6387_,
                    v___x_6388_,
                    v___y_6389_,
                    v___y_6390_,
                    v___y_6391_,
                    v___y_6392_,
                );
                if lean_obj_tag(v___x_6394_) == 0 {
                    lean_dec_ref_known(v___x_6394_, 1);
                    lean_inc(v_mvarId_6387_);
                    v___x_6395_ = l_Lean_MVarId_getType(
                        v_mvarId_6387_,
                        v___y_6389_,
                        v___y_6390_,
                        v___y_6391_,
                        v___y_6392_,
                    );
                    if lean_obj_tag(v___x_6395_) == 0 {
                        v_a_6396_ = lean_ctor_get(v___x_6395_, 0);
                        lean_inc(v_a_6396_);
                        lean_dec_ref_known(v___x_6395_, 1);
                        v___x_6397_ =
                            l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(
                                v_a_6396_,
                                v___y_6390_,
                            );
                        v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
                        lean_inc_n(v_a_6398_, 2);
                        lean_dec_ref(v___x_6397_);
                        v___x_6399_ = l_Lean_Meta_getLevel(
                            v_a_6398_,
                            v___y_6389_,
                            v___y_6390_,
                            v___y_6391_,
                            v___y_6392_,
                        );
                        if lean_obj_tag(v___x_6399_) == 0 {
                            v_a_6400_ = lean_ctor_get(v___x_6399_, 0);
                            lean_inc(v_a_6400_);
                            lean_dec_ref_known(v___x_6399_, 1);
                            lean_inc(v_mvarId_6387_);
                            v___x_6401_ = l_Lean_MVarId_getTag(
                                v_mvarId_6387_,
                                v___y_6389_,
                                v___y_6390_,
                                v___y_6391_,
                                v___y_6392_,
                            );
                            if lean_obj_tag(v___x_6401_) == 0 {
                                v_a_6402_ = lean_ctor_get(v___x_6401_, 0);
                                lean_inc(v_a_6402_);
                                lean_dec_ref_known(v___x_6401_, 1);
                                v___x_6403_ = lean_box(0);
                                v___x_6404_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_exfalso___lam__0___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_exfalso___lam__0___closed__2_once
                                    ),
                                    _init_l_Lean_MVarId_exfalso___lam__0___closed__2,
                                );
                                v___x_6405_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v___x_6404_,
                                    v_a_6402_,
                                    v___y_6389_,
                                    v___y_6390_,
                                    v___y_6391_,
                                    v___y_6392_,
                                );
                                if lean_obj_tag(v___x_6405_) == 0 {
                                    v_a_6406_ = lean_ctor_get(v___x_6405_, 0);
                                    lean_inc_n(v_a_6406_, 2);
                                    lean_dec_ref_known(v___x_6405_, 1);
                                    v___x_6407_ = l_Lean_MVarId_exfalso___lam__0___closed__4;
                                    v___x_6408_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_6408_, 0, v_a_6400_);
                                    lean_ctor_set(v___x_6408_, 1, v___x_6403_);
                                    v___x_6409_ = l_Lean_mkConst(v___x_6407_, v___x_6408_);
                                    v___x_6410_ = l_Lean_mkAppB(v___x_6409_, v_a_6398_, v_a_6406_);
                                    v___x_6411_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_6387_, v___x_6410_, v___y_6390_);
                                    v_isSharedCheck_6419_ = (!lean_is_exclusive(v___x_6411_)) as u8;
                                    if v_isSharedCheck_6419_ == 0 {
                                        v_unused_6420_ = lean_ctor_get(v___x_6411_, 0);
                                        lean_dec(v_unused_6420_);
                                        v___x_6413_ = v___x_6411_;
                                        v_isShared_6414_ = v_isSharedCheck_6419_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v___x_6411_);
                                        v___x_6413_ = lean_box(0);
                                        v_isShared_6414_ = v_isSharedCheck_6419_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_6400_);
                                    lean_dec(v_a_6398_);
                                    lean_dec(v_mvarId_6387_);
                                    v_a_6421_ = lean_ctor_get(v___x_6405_, 0);
                                    v_isSharedCheck_6428_ = (!lean_is_exclusive(v___x_6405_)) as u8;
                                    if v_isSharedCheck_6428_ == 0 {
                                        v___x_6423_ = v___x_6405_;
                                        v_isShared_6424_ = v_isSharedCheck_6428_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6421_);
                                        lean_dec(v___x_6405_);
                                        v___x_6423_ = lean_box(0);
                                        v_isShared_6424_ = v_isSharedCheck_6428_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6400_);
                                lean_dec(v_a_6398_);
                                lean_dec(v_mvarId_6387_);
                                v_a_6429_ = lean_ctor_get(v___x_6401_, 0);
                                v_isSharedCheck_6436_ = (!lean_is_exclusive(v___x_6401_)) as u8;
                                if v_isSharedCheck_6436_ == 0 {
                                    v___x_6431_ = v___x_6401_;
                                    v_isShared_6432_ = v_isSharedCheck_6436_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_6429_);
                                    lean_dec(v___x_6401_);
                                    v___x_6431_ = lean_box(0);
                                    v_isShared_6432_ = v_isSharedCheck_6436_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6398_);
                            lean_dec(v_mvarId_6387_);
                            v_a_6437_ = lean_ctor_get(v___x_6399_, 0);
                            v_isSharedCheck_6444_ = (!lean_is_exclusive(v___x_6399_)) as u8;
                            if v_isSharedCheck_6444_ == 0 {
                                v___x_6439_ = v___x_6399_;
                                v_isShared_6440_ = v_isSharedCheck_6444_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_6437_);
                                lean_dec(v___x_6399_);
                                v___x_6439_ = lean_box(0);
                                v_isShared_6440_ = v_isSharedCheck_6444_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_6387_);
                        v_a_6445_ = lean_ctor_get(v___x_6395_, 0);
                        v_isSharedCheck_6452_ = (!lean_is_exclusive(v___x_6395_)) as u8;
                        if v_isSharedCheck_6452_ == 0 {
                            v___x_6447_ = v___x_6395_;
                            v_isShared_6448_ = v_isSharedCheck_6452_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6445_);
                            lean_dec(v___x_6395_);
                            v___x_6447_ = lean_box(0);
                            v_isShared_6448_ = v_isSharedCheck_6452_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_6387_);
                    v_a_6453_ = lean_ctor_get(v___x_6394_, 0);
                    v_isSharedCheck_6460_ = (!lean_is_exclusive(v___x_6394_)) as u8;
                    if v_isSharedCheck_6460_ == 0 {
                        v___x_6455_ = v___x_6394_;
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6453_);
                        lean_dec(v___x_6394_);
                        v___x_6455_ = lean_box(0);
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6415_ = l_Lean_Expr_mvarId_x21(v_a_6406_);
                lean_dec(v_a_6406_);
                if v_isShared_6414_ == 0 {
                    lean_ctor_set(v___x_6413_, 0, v___x_6415_);
                    v___x_6417_ = v___x_6413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6418_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6418_, 0, v___x_6415_);
                    v___x_6417_ = v_reuseFailAlloc_6418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6417_;
            }
            3 => {
                if v_isShared_6424_ == 0 {
                    v___x_6426_ = v___x_6423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6427_, 0, v_a_6421_);
                    v___x_6426_ = v_reuseFailAlloc_6427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6426_;
            }
            5 => {
                if v_isShared_6432_ == 0 {
                    v___x_6434_ = v___x_6431_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6429_);
                    v___x_6434_ = v_reuseFailAlloc_6435_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6434_;
            }
            7 => {
                if v_isShared_6440_ == 0 {
                    v___x_6442_ = v___x_6439_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6443_, 0, v_a_6437_);
                    v___x_6442_ = v_reuseFailAlloc_6443_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6442_;
            }
            9 => {
                if v_isShared_6448_ == 0 {
                    v___x_6450_ = v___x_6447_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6451_, 0, v_a_6445_);
                    v___x_6450_ = v_reuseFailAlloc_6451_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6450_;
            }
            11 => {
                if v_isShared_6456_ == 0 {
                    v___x_6458_ = v___x_6455_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
                    v___x_6458_ = v_reuseFailAlloc_6459_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_exfalso___lam__0___boxed(
    mut v_mvarId_6461_: *mut LeanObject,
    mut v___x_6462_: *mut LeanObject,
    mut v___y_6463_: *mut LeanObject,
    mut v___y_6464_: *mut LeanObject,
    mut v___y_6465_: *mut LeanObject,
    mut v___y_6466_: *mut LeanObject,
    mut v___y_6467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6468_: *mut LeanObject = core::ptr::null_mut();
    v_res_6468_ = l_Lean_MVarId_exfalso___lam__0(
        v_mvarId_6461_,
        v___x_6462_,
        v___y_6463_,
        v___y_6464_,
        v___y_6465_,
        v___y_6466_,
    );
    lean_dec(v___y_6466_);
    lean_dec_ref(v___y_6465_);
    lean_dec(v___y_6464_);
    lean_dec_ref(v___y_6463_);
    return v_res_6468_;
}
pub unsafe fn l_Lean_MVarId_exfalso(
    mut v_mvarId_6472_: *mut LeanObject,
    mut v_a_6473_: *mut LeanObject,
    mut v_a_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
    mut v_a_6476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    v___x_6478_ = l_Lean_MVarId_exfalso___closed__1;
    lean_inc(v_mvarId_6472_);
    v___f_6479_ = lean_alloc_closure(
        l_Lean_MVarId_exfalso___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_6479_, 0, v_mvarId_6472_);
    lean_closure_set(v___f_6479_, 1, v___x_6478_);
    v___x_6480_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_6472_,
        v___f_6479_,
        v_a_6473_,
        v_a_6474_,
        v_a_6475_,
        v_a_6476_,
    );
    return v___x_6480_;
}
pub unsafe fn l_Lean_MVarId_exfalso___boxed(
    mut v_mvarId_6481_: *mut LeanObject,
    mut v_a_6482_: *mut LeanObject,
    mut v_a_6483_: *mut LeanObject,
    mut v_a_6484_: *mut LeanObject,
    mut v_a_6485_: *mut LeanObject,
    mut v_a_6486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6487_: *mut LeanObject = core::ptr::null_mut();
    v_res_6487_ = l_Lean_MVarId_exfalso(v_mvarId_6481_, v_a_6482_, v_a_6483_, v_a_6484_, v_a_6485_);
    lean_dec(v_a_6485_);
    lean_dec_ref(v_a_6484_);
    lean_dec(v_a_6483_);
    lean_dec_ref(v_a_6482_);
    return v_res_6487_;
}
pub unsafe fn _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    v___x_6491_ = l_Lean_MVarId_nthConstructor___lam__0___closed__1;
    v___x_6492_ = l_Lean_MessageData_ofFormat(v___x_6491_);
    return v___x_6492_;
}
pub unsafe fn _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    v___x_6493_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__2_once),
        _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2,
    );
    v___x_6494_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6494_, 0, v___x_6493_);
    return v___x_6494_;
}
pub unsafe fn l_Lean_MVarId_nthConstructor___lam__0(
    mut v_goal_6499_: *mut LeanObject,
    mut v_name_6500_: *mut LeanObject,
    mut v_idx_6501_: *mut LeanObject,
    mut v_expected_x3f_6502_: *mut LeanObject,
    mut v___y_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
    mut v___y_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: u8 = 0;
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6528_: u8 = 0;
    let mut v_val_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___y_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: u8 = 0;
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: u8 = 0;
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6567_: u8 = 0;
    let mut v_ctors_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: u8 = 0;
    let mut v___x_6571_: u8 = 0;
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut v_reuseFailAlloc_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6593_: u8 = 0;
    let mut v_isSharedCheck_6594_: u8 = 0;
    let mut v_isSharedCheck_6595_: u8 = 0;
    let mut v_a_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut v_a_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6607_: u8 = 0;
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_name_6500_);
                lean_inc(v_goal_6499_);
                v___x_6515_ = l_Lean_MVarId_checkNotAssigned(
                    v_goal_6499_,
                    v_name_6500_,
                    v___y_6503_,
                    v___y_6504_,
                    v___y_6505_,
                    v___y_6506_,
                );
                if lean_obj_tag(v___x_6515_) == 0 {
                    lean_dec_ref_known(v___x_6515_, 1);
                    lean_inc(v_goal_6499_);
                    v___x_6516_ = l_Lean_MVarId_getType_x27(
                        v_goal_6499_,
                        v___y_6503_,
                        v___y_6504_,
                        v___y_6505_,
                        v___y_6506_,
                    );
                    if lean_obj_tag(v___x_6516_) == 0 {
                        v_a_6517_ = lean_ctor_get(v___x_6516_, 0);
                        lean_inc(v_a_6517_);
                        lean_dec_ref_known(v___x_6516_, 1);
                        v___x_6518_ = l_Lean_Expr_getAppFn(v_a_6517_);
                        lean_dec(v_a_6517_);
                        if lean_obj_tag(v___x_6518_) == 4 {
                            v_declName_6519_ = lean_ctor_get(v___x_6518_, 0);
                            lean_inc(v_declName_6519_);
                            v_us_6520_ = lean_ctor_get(v___x_6518_, 1);
                            lean_inc(v_us_6520_);
                            lean_dec_ref_known(v___x_6518_, 2);
                            v___x_6521_ = lean_st_ref_get(v___y_6506_);
                            v_env_6522_ = lean_ctor_get(v___x_6521_, 0);
                            lean_inc_ref(v_env_6522_);
                            lean_dec(v___x_6521_);
                            v___x_6523_ = 0;
                            v___x_6524_ = l_Lean_Environment_find_x3f(
                                v_env_6522_,
                                v_declName_6519_,
                                v___x_6523_,
                            );
                            if lean_obj_tag(v___x_6524_) == 0 {
                                lean_dec(v_us_6520_);
                                lean_dec(v_expected_x3f_6502_);
                                lean_dec(v_idx_6501_);
                                v___y_6509_ = v___y_6503_;
                                v___y_6510_ = v___y_6504_;
                                v___y_6511_ = v___y_6505_;
                                v___y_6512_ = v___y_6506_;
                                state = 1;
                                continue;
                            } else {
                                v_val_6525_ = lean_ctor_get(v___x_6524_, 0);
                                v_isSharedCheck_6595_ = (!lean_is_exclusive(v___x_6524_)) as u8;
                                if v_isSharedCheck_6595_ == 0 {
                                    v___x_6527_ = v___x_6524_;
                                    v_isShared_6528_ = v_isSharedCheck_6595_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_val_6525_);
                                    lean_dec(v___x_6524_);
                                    v___x_6527_ = lean_box(0);
                                    v_isShared_6528_ = v_isSharedCheck_6595_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_6518_);
                            lean_dec(v_expected_x3f_6502_);
                            lean_dec(v_idx_6501_);
                            v___y_6509_ = v___y_6503_;
                            v___y_6510_ = v___y_6504_;
                            v___y_6511_ = v___y_6505_;
                            v___y_6512_ = v___y_6506_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_expected_x3f_6502_);
                        lean_dec(v_idx_6501_);
                        lean_dec(v_name_6500_);
                        lean_dec(v_goal_6499_);
                        v_a_6596_ = lean_ctor_get(v___x_6516_, 0);
                        v_isSharedCheck_6603_ = (!lean_is_exclusive(v___x_6516_)) as u8;
                        if v_isSharedCheck_6603_ == 0 {
                            v___x_6598_ = v___x_6516_;
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_6596_);
                            lean_dec(v___x_6516_);
                            v___x_6598_ = lean_box(0);
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_expected_x3f_6502_);
                    lean_dec(v_idx_6501_);
                    lean_dec(v_name_6500_);
                    lean_dec(v_goal_6499_);
                    v_a_6604_ = lean_ctor_get(v___x_6515_, 0);
                    v_isSharedCheck_6611_ = (!lean_is_exclusive(v___x_6515_)) as u8;
                    if v_isSharedCheck_6611_ == 0 {
                        v___x_6606_ = v___x_6515_;
                        v_isShared_6607_ = v_isSharedCheck_6611_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_6604_);
                        lean_dec(v___x_6515_);
                        v___x_6606_ = lean_box(0);
                        v_isShared_6607_ = v_isSharedCheck_6611_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6513_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3,
                );
                v___x_6514_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_6500_,
                    v_goal_6499_,
                    v___x_6513_,
                    v___y_6509_,
                    v___y_6510_,
                    v___y_6511_,
                    v___y_6512_,
                );
                return v___x_6514_;
            }
            2 => {
                if lean_obj_tag(v_val_6525_) == 5 {
                    v_val_6529_ = lean_ctor_get(v_val_6525_, 0);
                    v_isSharedCheck_6594_ = (!lean_is_exclusive(v_val_6525_)) as u8;
                    if v_isSharedCheck_6594_ == 0 {
                        v___x_6531_ = v_val_6525_;
                        v_isShared_6532_ = v_isSharedCheck_6594_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_6529_);
                        lean_dec(v_val_6525_);
                        v___x_6531_ = lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6594_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6527_);
                    lean_dec(v_val_6525_);
                    lean_dec(v_us_6520_);
                    lean_dec(v_expected_x3f_6502_);
                    lean_dec(v_idx_6501_);
                    v___y_6509_ = v___y_6503_;
                    v___y_6510_ = v___y_6504_;
                    v___y_6511_ = v___y_6505_;
                    v___y_6512_ = v___y_6506_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_expected_x3f_6502_) == 1 {
                    v_val_6564_ = lean_ctor_get(v_expected_x3f_6502_, 0);
                    v_isSharedCheck_6593_ = (!lean_is_exclusive(v_expected_x3f_6502_)) as u8;
                    if v_isSharedCheck_6593_ == 0 {
                        v___x_6566_ = v_expected_x3f_6502_;
                        v_isShared_6567_ = v_isSharedCheck_6593_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_6564_);
                        lean_dec(v_expected_x3f_6502_);
                        v___x_6566_ = lean_box(0);
                        v_isShared_6567_ = v_isSharedCheck_6593_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_expected_x3f_6502_);
                    v___y_6534_ = v___y_6503_;
                    v___y_6535_ = v___y_6504_;
                    v___y_6536_ = v___y_6505_;
                    v___y_6537_ = v___y_6506_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_ctors_6538_ = lean_ctor_get(v_val_6529_, 4);
                lean_inc(v_ctors_6538_);
                lean_dec_ref(v_val_6529_);
                v___x_6539_ = l_List_lengthTR___redArg(v_ctors_6538_);
                v___x_6540_ = lean_nat_dec_lt(v_idx_6501_, v___x_6539_);
                if v___x_6540_ == 0 {
                    lean_dec(v_ctors_6538_);
                    lean_dec(v_us_6520_);
                    v___x_6541_ = l_Lean_MVarId_nthConstructor___lam__0___closed__4;
                    v___x_6542_ = l_Nat_reprFast(v_idx_6501_);
                    v___x_6543_ = lean_string_append(v___x_6541_, v___x_6542_);
                    lean_dec_ref(v___x_6542_);
                    v___x_6544_ = l_Lean_MVarId_nthConstructor___lam__0___closed__5;
                    v___x_6545_ = lean_string_append(v___x_6543_, v___x_6544_);
                    v___x_6546_ = l_Nat_reprFast(v___x_6539_);
                    v___x_6547_ = lean_string_append(v___x_6545_, v___x_6546_);
                    lean_dec_ref(v___x_6546_);
                    v___x_6548_ = l_Lean_MVarId_nthConstructor___lam__0___closed__6;
                    v___x_6549_ = lean_string_append(v___x_6547_, v___x_6548_);
                    if v_isShared_6532_ == 0 {
                        lean_ctor_set_tag(v___x_6531_, 3);
                        lean_ctor_set(v___x_6531_, 0, v___x_6549_);
                        v___x_6551_ = v___x_6531_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6557_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6557_, 0, v___x_6549_);
                        v___x_6551_ = v_reuseFailAlloc_6557_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6539_);
                    lean_del_object(v___x_6531_);
                    lean_del_object(v___x_6527_);
                    lean_dec(v_name_6500_);
                    v___x_6558_ = l_List_get___redArg(v_ctors_6538_, v_idx_6501_);
                    lean_dec(v_ctors_6538_);
                    v___x_6559_ = l_Lean_mkConst(v___x_6558_, v_us_6520_);
                    v___x_6560_ = 0;
                    v___x_6561_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v___x_6561_, 0 as u32, v___x_6560_);
                    lean_ctor_set_uint8(v___x_6561_, 1 as u32, v___x_6540_);
                    lean_ctor_set_uint8(v___x_6561_, 2 as u32, v___x_6523_);
                    lean_ctor_set_uint8(v___x_6561_, 3 as u32, v___x_6540_);
                    v___x_6562_ = lean_box(0);
                    v___x_6563_ = l_Lean_MVarId_apply(
                        v_goal_6499_,
                        v___x_6559_,
                        v___x_6561_,
                        v___x_6562_,
                        v___y_6534_,
                        v___y_6535_,
                        v___y_6536_,
                        v___y_6537_,
                    );
                    return v___x_6563_;
                }
            }
            5 => {
                v___x_6552_ = l_Lean_MessageData_ofFormat(v___x_6551_);
                if v_isShared_6528_ == 0 {
                    lean_ctor_set(v___x_6527_, 0, v___x_6552_);
                    v___x_6554_ = v___x_6527_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6556_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6556_, 0, v___x_6552_);
                    v___x_6554_ = v_reuseFailAlloc_6556_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6555_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_6500_,
                    v_goal_6499_,
                    v___x_6554_,
                    v___y_6534_,
                    v___y_6535_,
                    v___y_6536_,
                    v___y_6537_,
                );
                return v___x_6555_;
            }
            7 => {
                v_ctors_6568_ = lean_ctor_get(v_val_6529_, 4);
                v___x_6569_ = l_List_lengthTR___redArg(v_ctors_6568_);
                v___x_6570_ = lean_nat_dec_eq(v___x_6569_, v_val_6564_);
                lean_dec(v___x_6569_);
                if v___x_6570_ == 0 {
                    v___x_6571_ = 1;
                    lean_inc(v_name_6500_);
                    v___x_6572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_6500_,
                        v___x_6571_,
                    );
                    v___x_6573_ = l_Lean_MVarId_nthConstructor___lam__0___closed__7;
                    v___x_6574_ = lean_string_append(v___x_6572_, v___x_6573_);
                    v___x_6575_ = l_Nat_reprFast(v_val_6564_);
                    v___x_6576_ = lean_string_append(v___x_6574_, v___x_6575_);
                    lean_dec_ref(v___x_6575_);
                    v___x_6577_ = l_Lean_MVarId_nthConstructor___lam__0___closed__6;
                    v___x_6578_ = lean_string_append(v___x_6576_, v___x_6577_);
                    v___x_6579_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_6579_, 0, v___x_6578_);
                    v___x_6580_ = l_Lean_MessageData_ofFormat(v___x_6579_);
                    if v_isShared_6567_ == 0 {
                        lean_ctor_set(v___x_6566_, 0, v___x_6580_);
                        v___x_6582_ = v___x_6566_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6592_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6592_, 0, v___x_6580_);
                        v___x_6582_ = v_reuseFailAlloc_6592_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6566_);
                    lean_dec(v_val_6564_);
                    v___y_6534_ = v___y_6503_;
                    v___y_6535_ = v___y_6504_;
                    v___y_6536_ = v___y_6505_;
                    v___y_6537_ = v___y_6506_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                lean_inc(v_goal_6499_);
                lean_inc(v_name_6500_);
                v___x_6583_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_6500_,
                    v_goal_6499_,
                    v___x_6582_,
                    v___y_6503_,
                    v___y_6504_,
                    v___y_6505_,
                    v___y_6506_,
                );
                if lean_obj_tag(v___x_6583_) == 0 {
                    lean_dec_ref_known(v___x_6583_, 1);
                    v___y_6534_ = v___y_6503_;
                    v___y_6535_ = v___y_6504_;
                    v___y_6536_ = v___y_6505_;
                    v___y_6537_ = v___y_6506_;
                    state = 4;
                    continue;
                } else {
                    lean_del_object(v___x_6531_);
                    lean_dec_ref(v_val_6529_);
                    lean_del_object(v___x_6527_);
                    lean_dec(v_us_6520_);
                    lean_dec(v_idx_6501_);
                    lean_dec(v_name_6500_);
                    lean_dec(v_goal_6499_);
                    v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
                    v_isSharedCheck_6591_ = (!lean_is_exclusive(v___x_6583_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6583_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6584_);
                        lean_dec(v___x_6583_);
                        v___x_6586_ = lean_box(0);
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_6587_ == 0 {
                    v___x_6589_ = v___x_6586_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
                    v___x_6589_ = v_reuseFailAlloc_6590_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6589_;
            }
            11 => {
                if v_isShared_6599_ == 0 {
                    v___x_6601_ = v___x_6598_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6602_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6601_;
            }
            13 => {
                if v_isShared_6607_ == 0 {
                    v___x_6609_ = v___x_6606_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6610_, 0, v_a_6604_);
                    v___x_6609_ = v_reuseFailAlloc_6610_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_nthConstructor___lam__0___boxed(
    mut v_goal_6612_: *mut LeanObject,
    mut v_name_6613_: *mut LeanObject,
    mut v_idx_6614_: *mut LeanObject,
    mut v_expected_x3f_6615_: *mut LeanObject,
    mut v___y_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
    mut v___y_6619_: *mut LeanObject,
    mut v___y_6620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6621_: *mut LeanObject = core::ptr::null_mut();
    v_res_6621_ = l_Lean_MVarId_nthConstructor___lam__0(
        v_goal_6612_,
        v_name_6613_,
        v_idx_6614_,
        v_expected_x3f_6615_,
        v___y_6616_,
        v___y_6617_,
        v___y_6618_,
        v___y_6619_,
    );
    lean_dec(v___y_6619_);
    lean_dec_ref(v___y_6618_);
    lean_dec(v___y_6617_);
    lean_dec_ref(v___y_6616_);
    return v_res_6621_;
}
pub unsafe fn l_Lean_MVarId_nthConstructor(
    mut v_name_6622_: *mut LeanObject,
    mut v_idx_6623_: *mut LeanObject,
    mut v_expected_x3f_6624_: *mut LeanObject,
    mut v_goal_6625_: *mut LeanObject,
    mut v_a_6626_: *mut LeanObject,
    mut v_a_6627_: *mut LeanObject,
    mut v_a_6628_: *mut LeanObject,
    mut v_a_6629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_6625_);
    v___f_6631_ = lean_alloc_closure(
        l_Lean_MVarId_nthConstructor___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_6631_, 0, v_goal_6625_);
    lean_closure_set(v___f_6631_, 1, v_name_6622_);
    lean_closure_set(v___f_6631_, 2, v_idx_6623_);
    lean_closure_set(v___f_6631_, 3, v_expected_x3f_6624_);
    v___x_6632_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_goal_6625_,
        v___f_6631_,
        v_a_6626_,
        v_a_6627_,
        v_a_6628_,
        v_a_6629_,
    );
    return v___x_6632_;
}
pub unsafe fn l_Lean_MVarId_nthConstructor___boxed(
    mut v_name_6633_: *mut LeanObject,
    mut v_idx_6634_: *mut LeanObject,
    mut v_expected_x3f_6635_: *mut LeanObject,
    mut v_goal_6636_: *mut LeanObject,
    mut v_a_6637_: *mut LeanObject,
    mut v_a_6638_: *mut LeanObject,
    mut v_a_6639_: *mut LeanObject,
    mut v_a_6640_: *mut LeanObject,
    mut v_a_6641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6642_: *mut LeanObject = core::ptr::null_mut();
    v_res_6642_ = l_Lean_MVarId_nthConstructor(
        v_name_6633_,
        v_idx_6634_,
        v_expected_x3f_6635_,
        v_goal_6636_,
        v_a_6637_,
        v_a_6638_,
        v_a_6639_,
        v_a_6640_,
    );
    lean_dec(v_a_6640_);
    lean_dec_ref(v_a_6639_);
    lean_dec(v_a_6638_);
    lean_dec_ref(v_a_6637_);
    return v_res_6642_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
    mut v_x_6643_: *mut LeanObject,
    mut v___y_6644_: *mut LeanObject,
    mut v___y_6645_: *mut LeanObject,
    mut v___y_6646_: *mut LeanObject,
    mut v___y_6647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6655_: u8 = 0;
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6660_: u8 = 0;
    let mut v_a_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6664_: u8 = 0;
    let mut v___y_6666_: u8 = 0;
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6670_: u8 = 0;
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6675_: u8 = 0;
    let mut v_unused_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6680_: u8 = 0;
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6684_: u8 = 0;
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: u8 = 0;
    let mut v___x_6689_: u8 = 0;
    let mut v_isSharedCheck_6690_: u8 = 0;
    let mut v_a_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6694_: u8 = 0;
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6649_ = l_Lean_Meta_saveState___redArg(v___y_6645_, v___y_6647_);
                if lean_obj_tag(v___x_6649_) == 0 {
                    v_a_6650_ = lean_ctor_get(v___x_6649_, 0);
                    lean_inc(v_a_6650_);
                    lean_dec_ref_known(v___x_6649_, 1);
                    lean_inc(v___y_6647_);
                    lean_inc_ref(v___y_6646_);
                    lean_inc(v___y_6645_);
                    lean_inc_ref(v___y_6644_);
                    v___x_6651_ = lean_apply_5(
                        v_x_6643_,
                        v___y_6644_,
                        v___y_6645_,
                        v___y_6646_,
                        v___y_6647_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6651_) == 0 {
                        lean_dec(v_a_6650_);
                        v_a_6652_ = lean_ctor_get(v___x_6651_, 0);
                        v_isSharedCheck_6660_ = (!lean_is_exclusive(v___x_6651_)) as u8;
                        if v_isSharedCheck_6660_ == 0 {
                            v___x_6654_ = v___x_6651_;
                            v_isShared_6655_ = v_isSharedCheck_6660_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6652_);
                            lean_dec(v___x_6651_);
                            v___x_6654_ = lean_box(0);
                            v_isShared_6655_ = v_isSharedCheck_6660_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6661_ = lean_ctor_get(v___x_6651_, 0);
                        v_isSharedCheck_6690_ = (!lean_is_exclusive(v___x_6651_)) as u8;
                        if v_isSharedCheck_6690_ == 0 {
                            v___x_6663_ = v___x_6651_;
                            v_isShared_6664_ = v_isSharedCheck_6690_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6661_);
                            lean_dec(v___x_6651_);
                            v___x_6663_ = lean_box(0);
                            v_isShared_6664_ = v_isSharedCheck_6690_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_6643_);
                    v_a_6691_ = lean_ctor_get(v___x_6649_, 0);
                    v_isSharedCheck_6698_ = (!lean_is_exclusive(v___x_6649_)) as u8;
                    if v_isSharedCheck_6698_ == 0 {
                        v___x_6693_ = v___x_6649_;
                        v_isShared_6694_ = v_isSharedCheck_6698_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6691_);
                        lean_dec(v___x_6649_);
                        v___x_6693_ = lean_box(0);
                        v_isShared_6694_ = v_isSharedCheck_6698_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6656_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6656_, 0, v_a_6652_);
                if v_isShared_6655_ == 0 {
                    lean_ctor_set(v___x_6654_, 0, v___x_6656_);
                    v___x_6658_ = v___x_6654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6659_, 0, v___x_6656_);
                    v___x_6658_ = v_reuseFailAlloc_6659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6658_;
            }
            3 => {
                v___x_6688_ = l_Lean_Exception_isInterrupt(v_a_6661_);
                if v___x_6688_ == 0 {
                    lean_inc(v_a_6661_);
                    v___x_6689_ = l_Lean_Exception_isRuntime(v_a_6661_);
                    v___y_6666_ = v___x_6689_;
                    state = 4;
                    continue;
                } else {
                    v___y_6666_ = v___x_6688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_6666_ == 0 {
                    lean_del_object(v___x_6663_);
                    lean_dec(v_a_6661_);
                    v___x_6667_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_6650_,
                        v___y_6645_,
                        v___y_6647_,
                    );
                    lean_dec(v_a_6650_);
                    if lean_obj_tag(v___x_6667_) == 0 {
                        v_isSharedCheck_6675_ = (!lean_is_exclusive(v___x_6667_)) as u8;
                        if v_isSharedCheck_6675_ == 0 {
                            v_unused_6676_ = lean_ctor_get(v___x_6667_, 0);
                            lean_dec(v_unused_6676_);
                            v___x_6669_ = v___x_6667_;
                            v_isShared_6670_ = v_isSharedCheck_6675_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_6667_);
                            v___x_6669_ = lean_box(0);
                            v_isShared_6670_ = v_isSharedCheck_6675_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_6677_ = lean_ctor_get(v___x_6667_, 0);
                        v_isSharedCheck_6684_ = (!lean_is_exclusive(v___x_6667_)) as u8;
                        if v_isSharedCheck_6684_ == 0 {
                            v___x_6679_ = v___x_6667_;
                            v_isShared_6680_ = v_isSharedCheck_6684_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6677_);
                            lean_dec(v___x_6667_);
                            v___x_6679_ = lean_box(0);
                            v_isShared_6680_ = v_isSharedCheck_6684_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6650_);
                    if v_isShared_6664_ == 0 {
                        v___x_6686_ = v___x_6663_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6687_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6687_, 0, v_a_6661_);
                        v___x_6686_ = v_reuseFailAlloc_6687_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6671_ = lean_box(0);
                if v_isShared_6670_ == 0 {
                    lean_ctor_set(v___x_6669_, 0, v___x_6671_);
                    v___x_6673_ = v___x_6669_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6674_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6674_, 0, v___x_6671_);
                    v___x_6673_ = v_reuseFailAlloc_6674_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6673_;
            }
            7 => {
                if v_isShared_6680_ == 0 {
                    v___x_6682_ = v___x_6679_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6683_, 0, v_a_6677_);
                    v___x_6682_ = v_reuseFailAlloc_6683_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6682_;
            }
            9 => {
                return v___x_6686_;
            }
            10 => {
                if v_isShared_6694_ == 0 {
                    v___x_6696_ = v___x_6693_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_a_6691_);
                    v___x_6696_ = v_reuseFailAlloc_6697_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(
    mut v_x_6699_: *mut LeanObject,
    mut v___y_6700_: *mut LeanObject,
    mut v___y_6701_: *mut LeanObject,
    mut v___y_6702_: *mut LeanObject,
    mut v___y_6703_: *mut LeanObject,
    mut v___y_6704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6705_: *mut LeanObject = core::ptr::null_mut();
    v_res_6705_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
        v_x_6699_,
        v___y_6700_,
        v___y_6701_,
        v___y_6702_,
        v___y_6703_,
    );
    lean_dec(v___y_6703_);
    lean_dec_ref(v___y_6702_);
    lean_dec(v___y_6701_);
    lean_dec_ref(v___y_6700_);
    return v_res_6705_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(
    mut v_00_u03b1_6706_: *mut LeanObject,
    mut v_x_6707_: *mut LeanObject,
    mut v___y_6708_: *mut LeanObject,
    mut v___y_6709_: *mut LeanObject,
    mut v___y_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    v___x_6713_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
        v_x_6707_,
        v___y_6708_,
        v___y_6709_,
        v___y_6710_,
        v___y_6711_,
    );
    return v___x_6713_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(
    mut v_00_u03b1_6714_: *mut LeanObject,
    mut v_x_6715_: *mut LeanObject,
    mut v___y_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
    mut v___y_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6721_: *mut LeanObject = core::ptr::null_mut();
    v_res_6721_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(
        v_00_u03b1_6714_,
        v_x_6715_,
        v___y_6716_,
        v___y_6717_,
        v___y_6718_,
        v___y_6719_,
    );
    lean_dec(v___y_6719_);
    lean_dec_ref(v___y_6718_);
    lean_dec(v___y_6717_);
    lean_dec_ref(v___y_6716_);
    return v_res_6721_;
}
pub unsafe fn _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    v___x_6723_ = l_Lean_MVarId_iffOfEq___lam__0___closed__0;
    v___x_6724_ = l_Lean_stringToMessageData(v___x_6723_);
    return v___x_6724_;
}
pub unsafe fn l_Lean_MVarId_iffOfEq___lam__0(
    mut v_mvarId_6725_: *mut LeanObject,
    mut v___x_6726_: *mut LeanObject,
    mut v___x_6727_: *mut LeanObject,
    mut v___x_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6738_: u8 = 0;
    let mut v___y_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_a_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6734_ = l_Lean_MVarId_apply(
                    v_mvarId_6725_,
                    v___x_6726_,
                    v___x_6727_,
                    v___x_6728_,
                    v___y_6729_,
                    v___y_6730_,
                    v___y_6731_,
                    v___y_6732_,
                );
                if lean_obj_tag(v___x_6734_) == 0 {
                    v_a_6735_ = lean_ctor_get(v___x_6734_, 0);
                    v_isSharedCheck_6751_ = (!lean_is_exclusive(v___x_6734_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v___x_6737_ = v___x_6734_;
                        v_isShared_6738_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6735_);
                        lean_dec(v___x_6734_);
                        v___x_6737_ = lean_box(0);
                        v_isShared_6738_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6752_ = lean_ctor_get(v___x_6734_, 0);
                    v_isSharedCheck_6759_ = (!lean_is_exclusive(v___x_6734_)) as u8;
                    if v_isSharedCheck_6759_ == 0 {
                        v___x_6754_ = v___x_6734_;
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6752_);
                        lean_dec(v___x_6734_);
                        v___x_6754_ = lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6735_) == 1 {
                    v_tail_6746_ = lean_ctor_get(v_a_6735_, 1);
                    if lean_obj_tag(v_tail_6746_) == 0 {
                        v_head_6747_ = lean_ctor_get(v_a_6735_, 0);
                        lean_inc(v_head_6747_);
                        lean_dec_ref_known(v_a_6735_, 2);
                        if v_isShared_6738_ == 0 {
                            lean_ctor_set(v___x_6737_, 0, v_head_6747_);
                            v___x_6749_ = v___x_6737_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6750_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_head_6747_);
                            v___x_6749_ = v_reuseFailAlloc_6750_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_6735_, 2);
                        lean_del_object(v___x_6737_);
                        v___y_6740_ = v___y_6729_;
                        v___y_6741_ = v___y_6730_;
                        v___y_6742_ = v___y_6731_;
                        v___y_6743_ = v___y_6732_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6737_);
                    lean_dec(v_a_6735_);
                    v___y_6740_ = v___y_6729_;
                    v___y_6741_ = v___y_6730_;
                    v___y_6742_ = v___y_6731_;
                    v___y_6743_ = v___y_6732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6744_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1_once),
                    _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                );
                v___x_6745_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                    v___x_6744_,
                    v___y_6740_,
                    v___y_6741_,
                    v___y_6742_,
                    v___y_6743_,
                );
                return v___x_6745_;
            }
            3 => {
                return v___x_6749_;
            }
            4 => {
                if v_isShared_6755_ == 0 {
                    v___x_6757_ = v___x_6754_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
                    v___x_6757_ = v_reuseFailAlloc_6758_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_iffOfEq___lam__0___boxed(
    mut v_mvarId_6760_: *mut LeanObject,
    mut v___x_6761_: *mut LeanObject,
    mut v___x_6762_: *mut LeanObject,
    mut v___x_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
    mut v___y_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6769_: *mut LeanObject = core::ptr::null_mut();
    v_res_6769_ = l_Lean_MVarId_iffOfEq___lam__0(
        v_mvarId_6760_,
        v___x_6761_,
        v___x_6762_,
        v___x_6763_,
        v___y_6764_,
        v___y_6765_,
        v___y_6766_,
        v___y_6767_,
    );
    lean_dec(v___y_6767_);
    lean_dec_ref(v___y_6766_);
    lean_dec(v___y_6765_);
    lean_dec_ref(v___y_6764_);
    return v_res_6769_;
}
pub unsafe fn _init_l_Lean_MVarId_iffOfEq___closed__2() -> *mut LeanObject {
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    v___x_6773_ = lean_box(0);
    v___x_6774_ = l_Lean_MVarId_iffOfEq___closed__1;
    v___x_6775_ = l_Lean_mkConst(v___x_6774_, v___x_6773_);
    return v___x_6775_;
}
pub unsafe fn l_Lean_MVarId_iffOfEq(
    mut v_mvarId_6780_: *mut LeanObject,
    mut v_a_6781_: *mut LeanObject,
    mut v_a_6782_: *mut LeanObject,
    mut v_a_6783_: *mut LeanObject,
    mut v_a_6784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6794_: u8 = 0;
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6802_: u8 = 0;
    let mut v_a_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6806_: u8 = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6786_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___closed__2_once),
                    _init_l_Lean_MVarId_iffOfEq___closed__2,
                );
                v___x_6787_ = l_Lean_MVarId_iffOfEq___closed__3;
                v___x_6788_ = lean_box(0);
                lean_inc(v_mvarId_6780_);
                v___f_6789_ = lean_alloc_closure(
                    l_Lean_MVarId_iffOfEq___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___f_6789_, 0, v_mvarId_6780_);
                lean_closure_set(v___f_6789_, 1, v___x_6786_);
                lean_closure_set(v___f_6789_, 2, v___x_6787_);
                lean_closure_set(v___f_6789_, 3, v___x_6788_);
                v___x_6790_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
                    v___f_6789_,
                    v_a_6781_,
                    v_a_6782_,
                    v_a_6783_,
                    v_a_6784_,
                );
                if lean_obj_tag(v___x_6790_) == 0 {
                    v_a_6791_ = lean_ctor_get(v___x_6790_, 0);
                    v_isSharedCheck_6802_ = (!lean_is_exclusive(v___x_6790_)) as u8;
                    if v_isSharedCheck_6802_ == 0 {
                        v___x_6793_ = v___x_6790_;
                        v_isShared_6794_ = v_isSharedCheck_6802_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6791_);
                        lean_dec(v___x_6790_);
                        v___x_6793_ = lean_box(0);
                        v_isShared_6794_ = v_isSharedCheck_6802_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_6780_);
                    v_a_6803_ = lean_ctor_get(v___x_6790_, 0);
                    v_isSharedCheck_6810_ = (!lean_is_exclusive(v___x_6790_)) as u8;
                    if v_isSharedCheck_6810_ == 0 {
                        v___x_6805_ = v___x_6790_;
                        v_isShared_6806_ = v_isSharedCheck_6810_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6803_);
                        lean_dec(v___x_6790_);
                        v___x_6805_ = lean_box(0);
                        v_isShared_6806_ = v_isSharedCheck_6810_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6791_) == 0 {
                    if v_isShared_6794_ == 0 {
                        lean_ctor_set(v___x_6793_, 0, v_mvarId_6780_);
                        v___x_6796_ = v___x_6793_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6797_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6797_, 0, v_mvarId_6780_);
                        v___x_6796_ = v_reuseFailAlloc_6797_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_6780_);
                    v_val_6798_ = lean_ctor_get(v_a_6791_, 0);
                    lean_inc(v_val_6798_);
                    lean_dec_ref_known(v_a_6791_, 1);
                    if v_isShared_6794_ == 0 {
                        lean_ctor_set(v___x_6793_, 0, v_val_6798_);
                        v___x_6800_ = v___x_6793_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6801_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6801_, 0, v_val_6798_);
                        v___x_6800_ = v_reuseFailAlloc_6801_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6796_;
            }
            3 => {
                return v___x_6800_;
            }
            4 => {
                if v_isShared_6806_ == 0 {
                    v___x_6808_ = v___x_6805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6809_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 0, v_a_6803_);
                    v___x_6808_ = v_reuseFailAlloc_6809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_iffOfEq___boxed(
    mut v_mvarId_6811_: *mut LeanObject,
    mut v_a_6812_: *mut LeanObject,
    mut v_a_6813_: *mut LeanObject,
    mut v_a_6814_: *mut LeanObject,
    mut v_a_6815_: *mut LeanObject,
    mut v_a_6816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6817_: *mut LeanObject = core::ptr::null_mut();
    v_res_6817_ = l_Lean_MVarId_iffOfEq(v_mvarId_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_);
    lean_dec(v_a_6815_);
    lean_dec_ref(v_a_6814_);
    lean_dec(v_a_6813_);
    lean_dec_ref(v_a_6812_);
    return v_res_6817_;
}
pub unsafe fn _init_l_Lean_MVarId_propext___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    v___x_6824_ = lean_box(0);
    v___x_6825_ = l_Lean_MVarId_propext___lam__0___closed__3;
    v___x_6826_ = l_Lean_mkConst(v___x_6825_, v___x_6824_);
    return v___x_6826_;
}
pub unsafe fn l_Lean_MVarId_propext___lam__0(
    mut v___x_6827_: u8,
    mut v_mvarId_6828_: *mut LeanObject,
    mut v___y_6829_: *mut LeanObject,
    mut v___y_6830_: *mut LeanObject,
    mut v___y_6831_: *mut LeanObject,
    mut v___y_6832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_6842_: u8 = 0;
    let mut v_ctxApprox_6843_: u8 = 0;
    let mut v_quasiPatternApprox_6844_: u8 = 0;
    let mut v_constApprox_6845_: u8 = 0;
    let mut v_isDefEqStuckEx_6846_: u8 = 0;
    let mut v_unificationHints_6847_: u8 = 0;
    let mut v_proofIrrelevance_6848_: u8 = 0;
    let mut v_assignSyntheticOpaque_6849_: u8 = 0;
    let mut v_offsetCnstrs_6850_: u8 = 0;
    let mut v_etaStruct_6851_: u8 = 0;
    let mut v_univApprox_6852_: u8 = 0;
    let mut v_iota_6853_: u8 = 0;
    let mut v_beta_6854_: u8 = 0;
    let mut v_proj_6855_: u8 = 0;
    let mut v_zeta_6856_: u8 = 0;
    let mut v_zetaDelta_6857_: u8 = 0;
    let mut v_zetaUnused_6858_: u8 = 0;
    let mut v_zetaHave_6859_: u8 = 0;
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6862_: u8 = 0;
    let mut v_trackZetaDelta_6863_: u8 = 0;
    let mut v_zetaDeltaSet_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6870_: u8 = 0;
    let mut v_inTypeClassResolution_6871_: u8 = 0;
    let mut v_cacheInferType_6872_: u8 = 0;
    let mut v_config_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: u64 = 0;
    let mut v___x_6876_: u64 = 0;
    let mut v___x_6877_: u64 = 0;
    let mut v___x_6878_: u64 = 0;
    let mut v___x_6879_: u64 = 0;
    let mut v_key_6880_: u64 = 0;
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: u8 = 0;
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: u8 = 0;
    let mut v___x_6891_: u8 = 0;
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6898_: u8 = 0;
    let mut v_tail_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_a_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6908_: u8 = 0;
    let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6912_: u8 = 0;
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: u8 = 0;
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6925_: u8 = 0;
    let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6929_: u8 = 0;
    let mut v_a_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6933_: u8 = 0;
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6937_: u8 = 0;
    let mut v_a_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6941_: u8 = 0;
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6945_: u8 = 0;
    let mut v_reuseFailAlloc_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6841_ = l_Lean_Meta_Context_config(v___y_6829_);
                v_foApprox_6842_ = lean_ctor_get_uint8(v___x_6841_, 0 as u32);
                v_ctxApprox_6843_ = lean_ctor_get_uint8(v___x_6841_, 1 as u32);
                v_quasiPatternApprox_6844_ = lean_ctor_get_uint8(v___x_6841_, 2 as u32);
                v_constApprox_6845_ = lean_ctor_get_uint8(v___x_6841_, 3 as u32);
                v_isDefEqStuckEx_6846_ = lean_ctor_get_uint8(v___x_6841_, 4 as u32);
                v_unificationHints_6847_ = lean_ctor_get_uint8(v___x_6841_, 5 as u32);
                v_proofIrrelevance_6848_ = lean_ctor_get_uint8(v___x_6841_, 6 as u32);
                v_assignSyntheticOpaque_6849_ = lean_ctor_get_uint8(v___x_6841_, 7 as u32);
                v_offsetCnstrs_6850_ = lean_ctor_get_uint8(v___x_6841_, 8 as u32);
                v_etaStruct_6851_ = lean_ctor_get_uint8(v___x_6841_, 10 as u32);
                v_univApprox_6852_ = lean_ctor_get_uint8(v___x_6841_, 11 as u32);
                v_iota_6853_ = lean_ctor_get_uint8(v___x_6841_, 12 as u32);
                v_beta_6854_ = lean_ctor_get_uint8(v___x_6841_, 13 as u32);
                v_proj_6855_ = lean_ctor_get_uint8(v___x_6841_, 14 as u32);
                v_zeta_6856_ = lean_ctor_get_uint8(v___x_6841_, 15 as u32);
                v_zetaDelta_6857_ = lean_ctor_get_uint8(v___x_6841_, 16 as u32);
                v_zetaUnused_6858_ = lean_ctor_get_uint8(v___x_6841_, 17 as u32);
                v_zetaHave_6859_ = lean_ctor_get_uint8(v___x_6841_, 18 as u32);
                v_isSharedCheck_6947_ = (!lean_is_exclusive(v___x_6841_)) as u8;
                if v_isSharedCheck_6947_ == 0 {
                    v___x_6861_ = v___x_6841_;
                    v_isShared_6862_ = v_isSharedCheck_6947_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_6841_);
                    v___x_6861_ = lean_box(0);
                    v_isShared_6862_ = v_isSharedCheck_6947_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6839_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1_once),
                    _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                );
                v___x_6840_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                    v___x_6839_,
                    v___y_6835_,
                    v___y_6836_,
                    v___y_6837_,
                    v___y_6838_,
                );
                return v___x_6840_;
            }
            2 => {
                v_trackZetaDelta_6863_ = lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_6864_ = lean_ctor_get(v___y_6829_, 1);
                v_lctx_6865_ = lean_ctor_get(v___y_6829_, 2);
                v_localInstances_6866_ = lean_ctor_get(v___y_6829_, 3);
                v_defEqCtx_x3f_6867_ = lean_ctor_get(v___y_6829_, 4);
                v_synthPendingDepth_6868_ = lean_ctor_get(v___y_6829_, 5);
                v_canUnfold_x3f_6869_ = lean_ctor_get(v___y_6829_, 6);
                v_univApprox_6870_ = lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_6871_ = lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_6872_ = lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_6862_ == 0 {
                    v_config_6874_ = v___x_6861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6946_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 0 as u32, v_foApprox_6842_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 1 as u32, v_ctxApprox_6843_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        2 as u32,
                        v_quasiPatternApprox_6844_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 3 as u32, v_constApprox_6845_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 4 as u32, v_isDefEqStuckEx_6846_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 5 as u32, v_unificationHints_6847_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 6 as u32, v_proofIrrelevance_6848_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        7 as u32,
                        v_assignSyntheticOpaque_6849_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 8 as u32, v_offsetCnstrs_6850_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 10 as u32, v_etaStruct_6851_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 11 as u32, v_univApprox_6852_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 12 as u32, v_iota_6853_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 13 as u32, v_beta_6854_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 14 as u32, v_proj_6855_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 15 as u32, v_zeta_6856_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 16 as u32, v_zetaDelta_6857_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 17 as u32, v_zetaUnused_6858_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6946_, 18 as u32, v_zetaHave_6859_);
                    v_config_6874_ = v_reuseFailAlloc_6946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_6874_, 9 as u32, v___x_6827_);
                v___x_6875_ = l_Lean_Meta_Context_configKey(v___y_6829_);
                v___x_6876_ = 3u64;
                v___x_6877_ = lean_uint64_shift_right(v___x_6875_, v___x_6876_);
                v___x_6878_ = lean_uint64_shift_left(v___x_6877_, v___x_6876_);
                v___x_6879_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_6827_);
                v_key_6880_ = lean_uint64_lor(v___x_6878_, v___x_6879_);
                v___x_6881_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_6881_, 0, v_config_6874_);
                lean_ctor_set_uint64(
                    v___x_6881_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_6880_,
                );
                lean_inc(v_canUnfold_x3f_6869_);
                lean_inc(v_synthPendingDepth_6868_);
                lean_inc(v_defEqCtx_x3f_6867_);
                lean_inc_ref(v_localInstances_6866_);
                lean_inc_ref(v_lctx_6865_);
                lean_inc(v_zetaDeltaSet_6864_);
                v___x_6882_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_6882_, 0, v___x_6881_);
                lean_ctor_set(v___x_6882_, 1, v_zetaDeltaSet_6864_);
                lean_ctor_set(v___x_6882_, 2, v_lctx_6865_);
                lean_ctor_set(v___x_6882_, 3, v_localInstances_6866_);
                lean_ctor_set(v___x_6882_, 4, v_defEqCtx_x3f_6867_);
                lean_ctor_set(v___x_6882_, 5, v_synthPendingDepth_6868_);
                lean_ctor_set(v___x_6882_, 6, v_canUnfold_x3f_6869_);
                lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_6863_,
                );
                lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_6870_,
                );
                lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_6871_,
                );
                lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_6872_,
                );
                lean_inc(v_mvarId_6828_);
                v___x_6883_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_6828_,
                    v___x_6882_,
                    v___y_6830_,
                    v___y_6831_,
                    v___y_6832_,
                );
                lean_dec_ref_known(v___x_6882_, 7);
                if lean_obj_tag(v___x_6883_) == 0 {
                    v_a_6884_ = lean_ctor_get(v___x_6883_, 0);
                    lean_inc(v_a_6884_);
                    lean_dec_ref_known(v___x_6883_, 1);
                    v___x_6885_ = l_Lean_MVarId_propext___lam__0___closed__1;
                    v___x_6886_ = lean_unsigned_to_nat(3);
                    v___x_6887_ = l_Lean_Expr_isAppOfArity(v_a_6884_, v___x_6885_, v___x_6886_);
                    if v___x_6887_ == 0 {
                        lean_dec(v_a_6884_);
                        lean_dec(v_mvarId_6828_);
                        v___x_6913_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                        );
                        v___x_6914_ =
                            l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                v___x_6913_,
                                v___y_6829_,
                                v___y_6830_,
                                v___y_6831_,
                                v___y_6832_,
                            );
                        return v___x_6914_;
                    } else {
                        v___x_6915_ = l_Lean_Expr_appFn_x21(v_a_6884_);
                        lean_dec(v_a_6884_);
                        v___x_6916_ = l_Lean_Expr_appArg_x21(v___x_6915_);
                        lean_dec_ref(v___x_6915_);
                        v___x_6917_ = l_Lean_Meta_isProp(
                            v___x_6916_,
                            v___y_6829_,
                            v___y_6830_,
                            v___y_6831_,
                            v___y_6832_,
                        );
                        if lean_obj_tag(v___x_6917_) == 0 {
                            v_a_6918_ = lean_ctor_get(v___x_6917_, 0);
                            lean_inc(v_a_6918_);
                            lean_dec_ref_known(v___x_6917_, 1);
                            v___x_6919_ = (lean_unbox(v_a_6918_) as u8);
                            lean_dec(v_a_6918_);
                            if v___x_6919_ == 0 {
                                lean_dec(v_mvarId_6828_);
                                v___x_6920_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_iffOfEq___lam__0___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                                    ),
                                    _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                                );
                                v___x_6921_ =
                                    l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                        v___x_6920_,
                                        v___y_6829_,
                                        v___y_6830_,
                                        v___y_6831_,
                                        v___y_6832_,
                                    );
                                v_a_6922_ = lean_ctor_get(v___x_6921_, 0);
                                v_isSharedCheck_6929_ = (!lean_is_exclusive(v___x_6921_)) as u8;
                                if v_isSharedCheck_6929_ == 0 {
                                    v___x_6924_ = v___x_6921_;
                                    v_isShared_6925_ = v_isSharedCheck_6929_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_6922_);
                                    lean_dec(v___x_6921_);
                                    v___x_6924_ = lean_box(0);
                                    v_isShared_6925_ = v_isSharedCheck_6929_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarId_6828_);
                            v_a_6930_ = lean_ctor_get(v___x_6917_, 0);
                            v_isSharedCheck_6937_ = (!lean_is_exclusive(v___x_6917_)) as u8;
                            if v_isSharedCheck_6937_ == 0 {
                                v___x_6932_ = v___x_6917_;
                                v_isShared_6933_ = v_isSharedCheck_6937_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_6930_);
                                lean_dec(v___x_6917_);
                                v___x_6932_ = lean_box(0);
                                v_isShared_6933_ = v_isSharedCheck_6937_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_mvarId_6828_);
                    v_a_6938_ = lean_ctor_get(v___x_6883_, 0);
                    v_isSharedCheck_6945_ = (!lean_is_exclusive(v___x_6883_)) as u8;
                    if v_isSharedCheck_6945_ == 0 {
                        v___x_6940_ = v___x_6883_;
                        v_isShared_6941_ = v_isSharedCheck_6945_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_6938_);
                        lean_dec(v___x_6883_);
                        v___x_6940_ = lean_box(0);
                        v_isShared_6941_ = v_isSharedCheck_6945_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6889_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_propext___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_propext___lam__0___closed__4_once),
                    _init_l_Lean_MVarId_propext___lam__0___closed__4,
                );
                v___x_6890_ = 0;
                v___x_6891_ = 0;
                v___x_6892_ = lean_alloc_ctor(0, 0, (4) as u32);
                lean_ctor_set_uint8(v___x_6892_, 0 as u32, v___x_6890_);
                lean_ctor_set_uint8(v___x_6892_, 1 as u32, v___x_6887_);
                lean_ctor_set_uint8(v___x_6892_, 2 as u32, v___x_6891_);
                lean_ctor_set_uint8(v___x_6892_, 3 as u32, v___x_6887_);
                v___x_6893_ = lean_box(0);
                v___x_6894_ = l_Lean_MVarId_apply(
                    v_mvarId_6828_,
                    v___x_6889_,
                    v___x_6892_,
                    v___x_6893_,
                    v___y_6829_,
                    v___y_6830_,
                    v___y_6831_,
                    v___y_6832_,
                );
                if lean_obj_tag(v___x_6894_) == 0 {
                    v_a_6895_ = lean_ctor_get(v___x_6894_, 0);
                    v_isSharedCheck_6904_ = (!lean_is_exclusive(v___x_6894_)) as u8;
                    if v_isSharedCheck_6904_ == 0 {
                        v___x_6897_ = v___x_6894_;
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6895_);
                        lean_dec(v___x_6894_);
                        v___x_6897_ = lean_box(0);
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_6905_ = lean_ctor_get(v___x_6894_, 0);
                    v_isSharedCheck_6912_ = (!lean_is_exclusive(v___x_6894_)) as u8;
                    if v_isSharedCheck_6912_ == 0 {
                        v___x_6907_ = v___x_6894_;
                        v_isShared_6908_ = v_isSharedCheck_6912_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6905_);
                        lean_dec(v___x_6894_);
                        v___x_6907_ = lean_box(0);
                        v_isShared_6908_ = v_isSharedCheck_6912_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_6895_) == 1 {
                    v_tail_6899_ = lean_ctor_get(v_a_6895_, 1);
                    if lean_obj_tag(v_tail_6899_) == 0 {
                        v_head_6900_ = lean_ctor_get(v_a_6895_, 0);
                        lean_inc(v_head_6900_);
                        lean_dec_ref_known(v_a_6895_, 2);
                        if v_isShared_6898_ == 0 {
                            lean_ctor_set(v___x_6897_, 0, v_head_6900_);
                            v___x_6902_ = v___x_6897_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6903_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_head_6900_);
                            v___x_6902_ = v_reuseFailAlloc_6903_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_6895_, 2);
                        lean_del_object(v___x_6897_);
                        v___y_6835_ = v___y_6829_;
                        v___y_6836_ = v___y_6830_;
                        v___y_6837_ = v___y_6831_;
                        v___y_6838_ = v___y_6832_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6897_);
                    lean_dec(v_a_6895_);
                    v___y_6835_ = v___y_6829_;
                    v___y_6836_ = v___y_6830_;
                    v___y_6837_ = v___y_6831_;
                    v___y_6838_ = v___y_6832_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                return v___x_6902_;
            }
            7 => {
                if v_isShared_6908_ == 0 {
                    v___x_6910_ = v___x_6907_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6911_, 0, v_a_6905_);
                    v___x_6910_ = v_reuseFailAlloc_6911_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6910_;
            }
            9 => {
                if v_isShared_6925_ == 0 {
                    v___x_6927_ = v___x_6924_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6928_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6928_, 0, v_a_6922_);
                    v___x_6927_ = v_reuseFailAlloc_6928_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6927_;
            }
            11 => {
                if v_isShared_6933_ == 0 {
                    v___x_6935_ = v___x_6932_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6936_, 0, v_a_6930_);
                    v___x_6935_ = v_reuseFailAlloc_6936_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6935_;
            }
            13 => {
                if v_isShared_6941_ == 0 {
                    v___x_6943_ = v___x_6940_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6944_, 0, v_a_6938_);
                    v___x_6943_ = v_reuseFailAlloc_6944_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_propext___lam__0___boxed(
    mut v___x_6948_: *mut LeanObject,
    mut v_mvarId_6949_: *mut LeanObject,
    mut v___y_6950_: *mut LeanObject,
    mut v___y_6951_: *mut LeanObject,
    mut v___y_6952_: *mut LeanObject,
    mut v___y_6953_: *mut LeanObject,
    mut v___y_6954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2435__boxed_6955_: u8 = 0;
    let mut v_res_6956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2435__boxed_6955_ = (lean_unbox(v___x_6948_) as u8);
    v_res_6956_ = l_Lean_MVarId_propext___lam__0(
        v___x_2435__boxed_6955_,
        v_mvarId_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
    );
    lean_dec(v___y_6953_);
    lean_dec_ref(v___y_6952_);
    lean_dec(v___y_6951_);
    lean_dec_ref(v___y_6950_);
    return v_res_6956_;
}
pub unsafe fn l_Lean_MVarId_propext(
    mut v_mvarId_6957_: *mut LeanObject,
    mut v_a_6958_: *mut LeanObject,
    mut v_a_6959_: *mut LeanObject,
    mut v_a_6960_: *mut LeanObject,
    mut v_a_6961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6963_: u8 = 0;
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6970_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6978_: u8 = 0;
    let mut v_a_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6982_: u8 = 0;
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6963_ = 2;
                v___x_6964_ = lean_box((v___x_6963_) as usize);
                lean_inc(v_mvarId_6957_);
                v___f_6965_ = lean_alloc_closure(
                    l_Lean_MVarId_propext___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_6965_, 0, v___x_6964_);
                lean_closure_set(v___f_6965_, 1, v_mvarId_6957_);
                v___x_6966_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
                    v___f_6965_,
                    v_a_6958_,
                    v_a_6959_,
                    v_a_6960_,
                    v_a_6961_,
                );
                if lean_obj_tag(v___x_6966_) == 0 {
                    v_a_6967_ = lean_ctor_get(v___x_6966_, 0);
                    v_isSharedCheck_6978_ = (!lean_is_exclusive(v___x_6966_)) as u8;
                    if v_isSharedCheck_6978_ == 0 {
                        v___x_6969_ = v___x_6966_;
                        v_isShared_6970_ = v_isSharedCheck_6978_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6967_);
                        lean_dec(v___x_6966_);
                        v___x_6969_ = lean_box(0);
                        v_isShared_6970_ = v_isSharedCheck_6978_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_6957_);
                    v_a_6979_ = lean_ctor_get(v___x_6966_, 0);
                    v_isSharedCheck_6986_ = (!lean_is_exclusive(v___x_6966_)) as u8;
                    if v_isSharedCheck_6986_ == 0 {
                        v___x_6981_ = v___x_6966_;
                        v_isShared_6982_ = v_isSharedCheck_6986_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6979_);
                        lean_dec(v___x_6966_);
                        v___x_6981_ = lean_box(0);
                        v_isShared_6982_ = v_isSharedCheck_6986_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6967_) == 0 {
                    if v_isShared_6970_ == 0 {
                        lean_ctor_set(v___x_6969_, 0, v_mvarId_6957_);
                        v___x_6972_ = v___x_6969_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6973_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6973_, 0, v_mvarId_6957_);
                        v___x_6972_ = v_reuseFailAlloc_6973_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_6957_);
                    v_val_6974_ = lean_ctor_get(v_a_6967_, 0);
                    lean_inc(v_val_6974_);
                    lean_dec_ref_known(v_a_6967_, 1);
                    if v_isShared_6970_ == 0 {
                        lean_ctor_set(v___x_6969_, 0, v_val_6974_);
                        v___x_6976_ = v___x_6969_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6977_, 0, v_val_6974_);
                        v___x_6976_ = v_reuseFailAlloc_6977_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6972_;
            }
            3 => {
                return v___x_6976_;
            }
            4 => {
                if v_isShared_6982_ == 0 {
                    v___x_6984_ = v___x_6981_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6985_, 0, v_a_6979_);
                    v___x_6984_ = v_reuseFailAlloc_6985_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_propext___boxed(
    mut v_mvarId_6987_: *mut LeanObject,
    mut v_a_6988_: *mut LeanObject,
    mut v_a_6989_: *mut LeanObject,
    mut v_a_6990_: *mut LeanObject,
    mut v_a_6991_: *mut LeanObject,
    mut v_a_6992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6993_: *mut LeanObject = core::ptr::null_mut();
    v_res_6993_ = l_Lean_MVarId_propext(v_mvarId_6987_, v_a_6988_, v_a_6989_, v_a_6990_, v_a_6991_);
    lean_dec(v_a_6991_);
    lean_dec_ref(v_a_6990_);
    lean_dec(v_a_6989_);
    lean_dec_ref(v_a_6988_);
    return v_res_6993_;
}
pub unsafe fn _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0() -> u64 {
    let mut v___x_6994_: u8 = 0;
    let mut v___x_6995_: u64 = 0;
    v___x_6994_ = 2;
    v___x_6995_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_6994_);
    return v___x_6995_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__0(
    mut v_mvarId_7002_: *mut LeanObject,
    mut v___x_7003_: *mut LeanObject,
    mut v___y_7004_: *mut LeanObject,
    mut v___y_7005_: *mut LeanObject,
    mut v___y_7006_: *mut LeanObject,
    mut v___y_7007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_7011_: u8 = 0;
    let mut v_ctxApprox_7012_: u8 = 0;
    let mut v_quasiPatternApprox_7013_: u8 = 0;
    let mut v_constApprox_7014_: u8 = 0;
    let mut v_isDefEqStuckEx_7015_: u8 = 0;
    let mut v_unificationHints_7016_: u8 = 0;
    let mut v_proofIrrelevance_7017_: u8 = 0;
    let mut v_assignSyntheticOpaque_7018_: u8 = 0;
    let mut v_offsetCnstrs_7019_: u8 = 0;
    let mut v_etaStruct_7020_: u8 = 0;
    let mut v_univApprox_7021_: u8 = 0;
    let mut v_iota_7022_: u8 = 0;
    let mut v_beta_7023_: u8 = 0;
    let mut v_proj_7024_: u8 = 0;
    let mut v_zeta_7025_: u8 = 0;
    let mut v_zetaDelta_7026_: u8 = 0;
    let mut v_zetaUnused_7027_: u8 = 0;
    let mut v_zetaHave_7028_: u8 = 0;
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7031_: u8 = 0;
    let mut v_trackZetaDelta_7032_: u8 = 0;
    let mut v_zetaDeltaSet_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7039_: u8 = 0;
    let mut v_inTypeClassResolution_7040_: u8 = 0;
    let mut v_cacheInferType_7041_: u8 = 0;
    let mut v___x_7042_: u8 = 0;
    let mut v_config_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: u64 = 0;
    let mut v___x_7046_: u64 = 0;
    let mut v___x_7047_: u64 = 0;
    let mut v___x_7048_: u64 = 0;
    let mut v___x_7049_: u64 = 0;
    let mut v_key_7050_: u64 = 0;
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: u8 = 0;
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7074_: u8 = 0;
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7079_: u8 = 0;
    let mut v_unused_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7084_: u8 = 0;
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7088_: u8 = 0;
    let mut v_a_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7092_: u8 = 0;
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7096_: u8 = 0;
    let mut v_reuseFailAlloc_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7098_: u8 = 0;
    let mut v_a_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7102_: u8 = 0;
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_7002_);
                v___x_7009_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7002_,
                    v___x_7003_,
                    v___y_7004_,
                    v___y_7005_,
                    v___y_7006_,
                    v___y_7007_,
                );
                if lean_obj_tag(v___x_7009_) == 0 {
                    lean_dec_ref_known(v___x_7009_, 1);
                    v___x_7010_ = l_Lean_Meta_Context_config(v___y_7004_);
                    v_foApprox_7011_ = lean_ctor_get_uint8(v___x_7010_, 0 as u32);
                    v_ctxApprox_7012_ = lean_ctor_get_uint8(v___x_7010_, 1 as u32);
                    v_quasiPatternApprox_7013_ = lean_ctor_get_uint8(v___x_7010_, 2 as u32);
                    v_constApprox_7014_ = lean_ctor_get_uint8(v___x_7010_, 3 as u32);
                    v_isDefEqStuckEx_7015_ = lean_ctor_get_uint8(v___x_7010_, 4 as u32);
                    v_unificationHints_7016_ = lean_ctor_get_uint8(v___x_7010_, 5 as u32);
                    v_proofIrrelevance_7017_ = lean_ctor_get_uint8(v___x_7010_, 6 as u32);
                    v_assignSyntheticOpaque_7018_ = lean_ctor_get_uint8(v___x_7010_, 7 as u32);
                    v_offsetCnstrs_7019_ = lean_ctor_get_uint8(v___x_7010_, 8 as u32);
                    v_etaStruct_7020_ = lean_ctor_get_uint8(v___x_7010_, 10 as u32);
                    v_univApprox_7021_ = lean_ctor_get_uint8(v___x_7010_, 11 as u32);
                    v_iota_7022_ = lean_ctor_get_uint8(v___x_7010_, 12 as u32);
                    v_beta_7023_ = lean_ctor_get_uint8(v___x_7010_, 13 as u32);
                    v_proj_7024_ = lean_ctor_get_uint8(v___x_7010_, 14 as u32);
                    v_zeta_7025_ = lean_ctor_get_uint8(v___x_7010_, 15 as u32);
                    v_zetaDelta_7026_ = lean_ctor_get_uint8(v___x_7010_, 16 as u32);
                    v_zetaUnused_7027_ = lean_ctor_get_uint8(v___x_7010_, 17 as u32);
                    v_zetaHave_7028_ = lean_ctor_get_uint8(v___x_7010_, 18 as u32);
                    v_isSharedCheck_7098_ = (!lean_is_exclusive(v___x_7010_)) as u8;
                    if v_isSharedCheck_7098_ == 0 {
                        v___x_7030_ = v___x_7010_;
                        v_isShared_7031_ = v_isSharedCheck_7098_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_7010_);
                        v___x_7030_ = lean_box(0);
                        v_isShared_7031_ = v_isSharedCheck_7098_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_7002_);
                    v_a_7099_ = lean_ctor_get(v___x_7009_, 0);
                    v_isSharedCheck_7106_ = (!lean_is_exclusive(v___x_7009_)) as u8;
                    if v_isSharedCheck_7106_ == 0 {
                        v___x_7101_ = v___x_7009_;
                        v_isShared_7102_ = v_isSharedCheck_7106_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_7099_);
                        lean_dec(v___x_7009_);
                        v___x_7101_ = lean_box(0);
                        v_isShared_7102_ = v_isSharedCheck_7106_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_7032_ = lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_7033_ = lean_ctor_get(v___y_7004_, 1);
                v_lctx_7034_ = lean_ctor_get(v___y_7004_, 2);
                v_localInstances_7035_ = lean_ctor_get(v___y_7004_, 3);
                v_defEqCtx_x3f_7036_ = lean_ctor_get(v___y_7004_, 4);
                v_synthPendingDepth_7037_ = lean_ctor_get(v___y_7004_, 5);
                v_canUnfold_x3f_7038_ = lean_ctor_get(v___y_7004_, 6);
                v_univApprox_7039_ = lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7040_ = lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7041_ = lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_7042_ = 2;
                if v_isShared_7031_ == 0 {
                    v_config_7044_ = v___x_7030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7097_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 0 as u32, v_foApprox_7011_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 1 as u32, v_ctxApprox_7012_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        2 as u32,
                        v_quasiPatternApprox_7013_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 3 as u32, v_constApprox_7014_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 4 as u32, v_isDefEqStuckEx_7015_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 5 as u32, v_unificationHints_7016_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 6 as u32, v_proofIrrelevance_7017_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        7 as u32,
                        v_assignSyntheticOpaque_7018_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 8 as u32, v_offsetCnstrs_7019_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 10 as u32, v_etaStruct_7020_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 11 as u32, v_univApprox_7021_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 12 as u32, v_iota_7022_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 13 as u32, v_beta_7023_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 14 as u32, v_proj_7024_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 15 as u32, v_zeta_7025_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 16 as u32, v_zetaDelta_7026_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 17 as u32, v_zetaUnused_7027_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7097_, 18 as u32, v_zetaHave_7028_);
                    v_config_7044_ = v_reuseFailAlloc_7097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_7044_, 9 as u32, v___x_7042_);
                v___x_7045_ = l_Lean_Meta_Context_configKey(v___y_7004_);
                v___x_7046_ = 3u64;
                v___x_7047_ = lean_uint64_shift_right(v___x_7045_, v___x_7046_);
                v___x_7048_ = lean_uint64_shift_left(v___x_7047_, v___x_7046_);
                v___x_7049_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once),
                    _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0,
                );
                v_key_7050_ = lean_uint64_lor(v___x_7048_, v___x_7049_);
                v___x_7051_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_7051_, 0, v_config_7044_);
                lean_ctor_set_uint64(
                    v___x_7051_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_7050_,
                );
                lean_inc(v_canUnfold_x3f_7038_);
                lean_inc(v_synthPendingDepth_7037_);
                lean_inc(v_defEqCtx_x3f_7036_);
                lean_inc_ref(v_localInstances_7035_);
                lean_inc_ref(v_lctx_7034_);
                lean_inc(v_zetaDeltaSet_7033_);
                v___x_7052_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_7052_, 0, v___x_7051_);
                lean_ctor_set(v___x_7052_, 1, v_zetaDeltaSet_7033_);
                lean_ctor_set(v___x_7052_, 2, v_lctx_7034_);
                lean_ctor_set(v___x_7052_, 3, v_localInstances_7035_);
                lean_ctor_set(v___x_7052_, 4, v_defEqCtx_x3f_7036_);
                lean_ctor_set(v___x_7052_, 5, v_synthPendingDepth_7037_);
                lean_ctor_set(v___x_7052_, 6, v_canUnfold_x3f_7038_);
                lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_7032_,
                );
                lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7039_,
                );
                lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7040_,
                );
                lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7041_,
                );
                lean_inc(v_mvarId_7002_);
                v___x_7053_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_7002_,
                    v___x_7052_,
                    v___y_7005_,
                    v___y_7006_,
                    v___y_7007_,
                );
                lean_dec_ref_known(v___x_7052_, 7);
                if lean_obj_tag(v___x_7053_) == 0 {
                    v_a_7054_ = lean_ctor_get(v___x_7053_, 0);
                    lean_inc(v_a_7054_);
                    lean_dec_ref_known(v___x_7053_, 1);
                    v___x_7055_ = l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2;
                    v___x_7056_ = lean_unsigned_to_nat(4);
                    v___x_7057_ = l_Lean_Expr_isAppOfArity(v_a_7054_, v___x_7055_, v___x_7056_);
                    if v___x_7057_ == 0 {
                        lean_dec(v_a_7054_);
                        lean_dec(v_mvarId_7002_);
                        v___x_7058_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                        );
                        v___x_7059_ =
                            l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                v___x_7058_,
                                v___y_7004_,
                                v___y_7005_,
                                v___y_7006_,
                                v___y_7007_,
                            );
                        return v___x_7059_;
                    } else {
                        v___x_7060_ = l_Lean_Expr_appFn_x21(v_a_7054_);
                        v___x_7061_ = l_Lean_Expr_appFn_x21(v___x_7060_);
                        lean_dec_ref(v___x_7060_);
                        v___x_7062_ = l_Lean_Expr_appArg_x21(v___x_7061_);
                        lean_dec_ref(v___x_7061_);
                        v___x_7063_ = l_Lean_Expr_appArg_x21(v_a_7054_);
                        lean_dec(v_a_7054_);
                        v___x_7064_ = l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4;
                        v___x_7065_ = lean_unsigned_to_nat(2);
                        v___x_7066_ = lean_mk_empty_array_with_capacity(v___x_7065_);
                        v___x_7067_ = lean_array_push(v___x_7066_, v___x_7062_);
                        v___x_7068_ = lean_array_push(v___x_7067_, v___x_7063_);
                        v___x_7069_ = l_Lean_Meta_mkAppM(
                            v___x_7064_,
                            v___x_7068_,
                            v___y_7004_,
                            v___y_7005_,
                            v___y_7006_,
                            v___y_7007_,
                        );
                        if lean_obj_tag(v___x_7069_) == 0 {
                            v_a_7070_ = lean_ctor_get(v___x_7069_, 0);
                            lean_inc(v_a_7070_);
                            lean_dec_ref_known(v___x_7069_, 1);
                            v___x_7071_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                    v_mvarId_7002_,
                                    v_a_7070_,
                                    v___y_7005_,
                                );
                            v_isSharedCheck_7079_ = (!lean_is_exclusive(v___x_7071_)) as u8;
                            if v_isSharedCheck_7079_ == 0 {
                                v_unused_7080_ = lean_ctor_get(v___x_7071_, 0);
                                lean_dec(v_unused_7080_);
                                v___x_7073_ = v___x_7071_;
                                v_isShared_7074_ = v_isSharedCheck_7079_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_7071_);
                                v___x_7073_ = lean_box(0);
                                v_isShared_7074_ = v_isSharedCheck_7079_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarId_7002_);
                            v_a_7081_ = lean_ctor_get(v___x_7069_, 0);
                            v_isSharedCheck_7088_ = (!lean_is_exclusive(v___x_7069_)) as u8;
                            if v_isSharedCheck_7088_ == 0 {
                                v___x_7083_ = v___x_7069_;
                                v_isShared_7084_ = v_isSharedCheck_7088_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_7081_);
                                lean_dec(v___x_7069_);
                                v___x_7083_ = lean_box(0);
                                v_isShared_7084_ = v_isSharedCheck_7088_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_mvarId_7002_);
                    v_a_7089_ = lean_ctor_get(v___x_7053_, 0);
                    v_isSharedCheck_7096_ = (!lean_is_exclusive(v___x_7053_)) as u8;
                    if v_isSharedCheck_7096_ == 0 {
                        v___x_7091_ = v___x_7053_;
                        v_isShared_7092_ = v_isSharedCheck_7096_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_7089_);
                        lean_dec(v___x_7053_);
                        v___x_7091_ = lean_box(0);
                        v_isShared_7092_ = v_isSharedCheck_7096_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7075_ = lean_box((v___x_7057_) as usize);
                if v_isShared_7074_ == 0 {
                    lean_ctor_set(v___x_7073_, 0, v___x_7075_);
                    v___x_7077_ = v___x_7073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7078_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7078_, 0, v___x_7075_);
                    v___x_7077_ = v_reuseFailAlloc_7078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7077_;
            }
            5 => {
                if v_isShared_7084_ == 0 {
                    v___x_7086_ = v___x_7083_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7087_, 0, v_a_7081_);
                    v___x_7086_ = v_reuseFailAlloc_7087_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7086_;
            }
            7 => {
                if v_isShared_7092_ == 0 {
                    v___x_7094_ = v___x_7091_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7095_, 0, v_a_7089_);
                    v___x_7094_ = v_reuseFailAlloc_7095_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7094_;
            }
            9 => {
                if v_isShared_7102_ == 0 {
                    v___x_7104_ = v___x_7101_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_a_7099_);
                    v___x_7104_ = v_reuseFailAlloc_7105_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(
    mut v_mvarId_7107_: *mut LeanObject,
    mut v___x_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
    mut v___y_7111_: *mut LeanObject,
    mut v___y_7112_: *mut LeanObject,
    mut v___y_7113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7114_: *mut LeanObject = core::ptr::null_mut();
    v_res_7114_ = l_Lean_MVarId_proofIrrelHeq___lam__0(
        v_mvarId_7107_,
        v___x_7108_,
        v___y_7109_,
        v___y_7110_,
        v___y_7111_,
        v___y_7112_,
    );
    lean_dec(v___y_7112_);
    lean_dec_ref(v___y_7111_);
    lean_dec(v___y_7110_);
    lean_dec_ref(v___y_7109_);
    return v_res_7114_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__1(
    mut v___f_7115_: *mut LeanObject,
    mut v___y_7116_: *mut LeanObject,
    mut v___y_7117_: *mut LeanObject,
    mut v___y_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7125_: u8 = 0;
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7135_: u8 = 0;
    let mut v_a_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7139_: u8 = 0;
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7121_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
                    v___f_7115_,
                    v___y_7116_,
                    v___y_7117_,
                    v___y_7118_,
                    v___y_7119_,
                );
                if lean_obj_tag(v___x_7121_) == 0 {
                    v_a_7122_ = lean_ctor_get(v___x_7121_, 0);
                    v_isSharedCheck_7135_ = (!lean_is_exclusive(v___x_7121_)) as u8;
                    if v_isSharedCheck_7135_ == 0 {
                        v___x_7124_ = v___x_7121_;
                        v_isShared_7125_ = v_isSharedCheck_7135_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7122_);
                        lean_dec(v___x_7121_);
                        v___x_7124_ = lean_box(0);
                        v_isShared_7125_ = v_isSharedCheck_7135_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7136_ = lean_ctor_get(v___x_7121_, 0);
                    v_isSharedCheck_7143_ = (!lean_is_exclusive(v___x_7121_)) as u8;
                    if v_isSharedCheck_7143_ == 0 {
                        v___x_7138_ = v___x_7121_;
                        v_isShared_7139_ = v_isSharedCheck_7143_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_7136_);
                        lean_dec(v___x_7121_);
                        v___x_7138_ = lean_box(0);
                        v_isShared_7139_ = v_isSharedCheck_7143_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7122_) == 0 {
                    v___x_7126_ = 0;
                    v___x_7127_ = lean_box((v___x_7126_) as usize);
                    if v_isShared_7125_ == 0 {
                        lean_ctor_set(v___x_7124_, 0, v___x_7127_);
                        v___x_7129_ = v___x_7124_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7130_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7130_, 0, v___x_7127_);
                        v___x_7129_ = v_reuseFailAlloc_7130_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_7131_ = lean_ctor_get(v_a_7122_, 0);
                    lean_inc(v_val_7131_);
                    lean_dec_ref_known(v_a_7122_, 1);
                    if v_isShared_7125_ == 0 {
                        lean_ctor_set(v___x_7124_, 0, v_val_7131_);
                        v___x_7133_ = v___x_7124_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7134_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7134_, 0, v_val_7131_);
                        v___x_7133_ = v_reuseFailAlloc_7134_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7129_;
            }
            3 => {
                return v___x_7133_;
            }
            4 => {
                if v_isShared_7139_ == 0 {
                    v___x_7141_ = v___x_7138_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7142_, 0, v_a_7136_);
                    v___x_7141_ = v_reuseFailAlloc_7142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(
    mut v___f_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
    mut v___y_7146_: *mut LeanObject,
    mut v___y_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
    mut v___y_7149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7150_: *mut LeanObject = core::ptr::null_mut();
    v_res_7150_ = l_Lean_MVarId_proofIrrelHeq___lam__1(
        v___f_7144_,
        v___y_7145_,
        v___y_7146_,
        v___y_7147_,
        v___y_7148_,
    );
    lean_dec(v___y_7148_);
    lean_dec_ref(v___y_7147_);
    lean_dec(v___y_7146_);
    lean_dec_ref(v___y_7145_);
    return v_res_7150_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq(
    mut v_mvarId_7154_: *mut LeanObject,
    mut v_a_7155_: *mut LeanObject,
    mut v_a_7156_: *mut LeanObject,
    mut v_a_7157_: *mut LeanObject,
    mut v_a_7158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    v___x_7160_ = l_Lean_MVarId_proofIrrelHeq___closed__1;
    lean_inc(v_mvarId_7154_);
    v___f_7161_ = lean_alloc_closure(
        l_Lean_MVarId_proofIrrelHeq___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_7161_, 0, v_mvarId_7154_);
    lean_closure_set(v___f_7161_, 1, v___x_7160_);
    v___f_7162_ = lean_alloc_closure(
        l_Lean_MVarId_proofIrrelHeq___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_7162_, 0, v___f_7161_);
    v___x_7163_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_7154_,
        v___f_7162_,
        v_a_7155_,
        v_a_7156_,
        v_a_7157_,
        v_a_7158_,
    );
    return v___x_7163_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___boxed(
    mut v_mvarId_7164_: *mut LeanObject,
    mut v_a_7165_: *mut LeanObject,
    mut v_a_7166_: *mut LeanObject,
    mut v_a_7167_: *mut LeanObject,
    mut v_a_7168_: *mut LeanObject,
    mut v_a_7169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7170_: *mut LeanObject = core::ptr::null_mut();
    v_res_7170_ =
        l_Lean_MVarId_proofIrrelHeq(v_mvarId_7164_, v_a_7165_, v_a_7166_, v_a_7167_, v_a_7168_);
    lean_dec(v_a_7168_);
    lean_dec_ref(v_a_7167_);
    lean_dec(v_a_7166_);
    lean_dec_ref(v_a_7165_);
    return v_res_7170_;
}
pub unsafe fn l_Lean_MVarId_subsingletonElim___lam__0(
    mut v_mvarId_7175_: *mut LeanObject,
    mut v___x_7176_: *mut LeanObject,
    mut v___y_7177_: *mut LeanObject,
    mut v___y_7178_: *mut LeanObject,
    mut v___y_7179_: *mut LeanObject,
    mut v___y_7180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_7184_: u8 = 0;
    let mut v_ctxApprox_7185_: u8 = 0;
    let mut v_quasiPatternApprox_7186_: u8 = 0;
    let mut v_constApprox_7187_: u8 = 0;
    let mut v_isDefEqStuckEx_7188_: u8 = 0;
    let mut v_unificationHints_7189_: u8 = 0;
    let mut v_proofIrrelevance_7190_: u8 = 0;
    let mut v_assignSyntheticOpaque_7191_: u8 = 0;
    let mut v_offsetCnstrs_7192_: u8 = 0;
    let mut v_etaStruct_7193_: u8 = 0;
    let mut v_univApprox_7194_: u8 = 0;
    let mut v_iota_7195_: u8 = 0;
    let mut v_beta_7196_: u8 = 0;
    let mut v_proj_7197_: u8 = 0;
    let mut v_zeta_7198_: u8 = 0;
    let mut v_zetaDelta_7199_: u8 = 0;
    let mut v_zetaUnused_7200_: u8 = 0;
    let mut v_zetaHave_7201_: u8 = 0;
    let mut v___x_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7204_: u8 = 0;
    let mut v_trackZetaDelta_7205_: u8 = 0;
    let mut v_zetaDeltaSet_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7212_: u8 = 0;
    let mut v_inTypeClassResolution_7213_: u8 = 0;
    let mut v_cacheInferType_7214_: u8 = 0;
    let mut v___x_7215_: u8 = 0;
    let mut v_config_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: u64 = 0;
    let mut v___x_7219_: u64 = 0;
    let mut v___x_7220_: u64 = 0;
    let mut v___x_7221_: u64 = 0;
    let mut v___x_7222_: u64 = 0;
    let mut v_key_7223_: u64 = 0;
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: u8 = 0;
    let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7246_: u8 = 0;
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7251_: u8 = 0;
    let mut v_unused_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7256_: u8 = 0;
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7260_: u8 = 0;
    let mut v_a_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7264_: u8 = 0;
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7268_: u8 = 0;
    let mut v_reuseFailAlloc_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7270_: u8 = 0;
    let mut v_a_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7274_: u8 = 0;
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_7175_);
                v___x_7182_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7175_,
                    v___x_7176_,
                    v___y_7177_,
                    v___y_7178_,
                    v___y_7179_,
                    v___y_7180_,
                );
                if lean_obj_tag(v___x_7182_) == 0 {
                    lean_dec_ref_known(v___x_7182_, 1);
                    v___x_7183_ = l_Lean_Meta_Context_config(v___y_7177_);
                    v_foApprox_7184_ = lean_ctor_get_uint8(v___x_7183_, 0 as u32);
                    v_ctxApprox_7185_ = lean_ctor_get_uint8(v___x_7183_, 1 as u32);
                    v_quasiPatternApprox_7186_ = lean_ctor_get_uint8(v___x_7183_, 2 as u32);
                    v_constApprox_7187_ = lean_ctor_get_uint8(v___x_7183_, 3 as u32);
                    v_isDefEqStuckEx_7188_ = lean_ctor_get_uint8(v___x_7183_, 4 as u32);
                    v_unificationHints_7189_ = lean_ctor_get_uint8(v___x_7183_, 5 as u32);
                    v_proofIrrelevance_7190_ = lean_ctor_get_uint8(v___x_7183_, 6 as u32);
                    v_assignSyntheticOpaque_7191_ = lean_ctor_get_uint8(v___x_7183_, 7 as u32);
                    v_offsetCnstrs_7192_ = lean_ctor_get_uint8(v___x_7183_, 8 as u32);
                    v_etaStruct_7193_ = lean_ctor_get_uint8(v___x_7183_, 10 as u32);
                    v_univApprox_7194_ = lean_ctor_get_uint8(v___x_7183_, 11 as u32);
                    v_iota_7195_ = lean_ctor_get_uint8(v___x_7183_, 12 as u32);
                    v_beta_7196_ = lean_ctor_get_uint8(v___x_7183_, 13 as u32);
                    v_proj_7197_ = lean_ctor_get_uint8(v___x_7183_, 14 as u32);
                    v_zeta_7198_ = lean_ctor_get_uint8(v___x_7183_, 15 as u32);
                    v_zetaDelta_7199_ = lean_ctor_get_uint8(v___x_7183_, 16 as u32);
                    v_zetaUnused_7200_ = lean_ctor_get_uint8(v___x_7183_, 17 as u32);
                    v_zetaHave_7201_ = lean_ctor_get_uint8(v___x_7183_, 18 as u32);
                    v_isSharedCheck_7270_ = (!lean_is_exclusive(v___x_7183_)) as u8;
                    if v_isSharedCheck_7270_ == 0 {
                        v___x_7203_ = v___x_7183_;
                        v_isShared_7204_ = v_isSharedCheck_7270_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_7183_);
                        v___x_7203_ = lean_box(0);
                        v_isShared_7204_ = v_isSharedCheck_7270_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_7175_);
                    v_a_7271_ = lean_ctor_get(v___x_7182_, 0);
                    v_isSharedCheck_7278_ = (!lean_is_exclusive(v___x_7182_)) as u8;
                    if v_isSharedCheck_7278_ == 0 {
                        v___x_7273_ = v___x_7182_;
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_7271_);
                        lean_dec(v___x_7182_);
                        v___x_7273_ = lean_box(0);
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_7205_ = lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_7206_ = lean_ctor_get(v___y_7177_, 1);
                v_lctx_7207_ = lean_ctor_get(v___y_7177_, 2);
                v_localInstances_7208_ = lean_ctor_get(v___y_7177_, 3);
                v_defEqCtx_x3f_7209_ = lean_ctor_get(v___y_7177_, 4);
                v_synthPendingDepth_7210_ = lean_ctor_get(v___y_7177_, 5);
                v_canUnfold_x3f_7211_ = lean_ctor_get(v___y_7177_, 6);
                v_univApprox_7212_ = lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7213_ = lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7214_ = lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_7215_ = 2;
                if v_isShared_7204_ == 0 {
                    v_config_7217_ = v___x_7203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7269_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 0 as u32, v_foApprox_7184_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 1 as u32, v_ctxApprox_7185_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        2 as u32,
                        v_quasiPatternApprox_7186_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 3 as u32, v_constApprox_7187_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 4 as u32, v_isDefEqStuckEx_7188_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 5 as u32, v_unificationHints_7189_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 6 as u32, v_proofIrrelevance_7190_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        7 as u32,
                        v_assignSyntheticOpaque_7191_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 8 as u32, v_offsetCnstrs_7192_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 10 as u32, v_etaStruct_7193_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 11 as u32, v_univApprox_7194_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 12 as u32, v_iota_7195_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 13 as u32, v_beta_7196_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 14 as u32, v_proj_7197_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 15 as u32, v_zeta_7198_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 16 as u32, v_zetaDelta_7199_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 17 as u32, v_zetaUnused_7200_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7269_, 18 as u32, v_zetaHave_7201_);
                    v_config_7217_ = v_reuseFailAlloc_7269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_7217_, 9 as u32, v___x_7215_);
                v___x_7218_ = l_Lean_Meta_Context_configKey(v___y_7177_);
                v___x_7219_ = 3u64;
                v___x_7220_ = lean_uint64_shift_right(v___x_7218_, v___x_7219_);
                v___x_7221_ = lean_uint64_shift_left(v___x_7220_, v___x_7219_);
                v___x_7222_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once),
                    _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0,
                );
                v_key_7223_ = lean_uint64_lor(v___x_7221_, v___x_7222_);
                v___x_7224_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_7224_, 0, v_config_7217_);
                lean_ctor_set_uint64(
                    v___x_7224_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_7223_,
                );
                lean_inc(v_canUnfold_x3f_7211_);
                lean_inc(v_synthPendingDepth_7210_);
                lean_inc(v_defEqCtx_x3f_7209_);
                lean_inc_ref(v_localInstances_7208_);
                lean_inc_ref(v_lctx_7207_);
                lean_inc(v_zetaDeltaSet_7206_);
                v___x_7225_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_7225_, 0, v___x_7224_);
                lean_ctor_set(v___x_7225_, 1, v_zetaDeltaSet_7206_);
                lean_ctor_set(v___x_7225_, 2, v_lctx_7207_);
                lean_ctor_set(v___x_7225_, 3, v_localInstances_7208_);
                lean_ctor_set(v___x_7225_, 4, v_defEqCtx_x3f_7209_);
                lean_ctor_set(v___x_7225_, 5, v_synthPendingDepth_7210_);
                lean_ctor_set(v___x_7225_, 6, v_canUnfold_x3f_7211_);
                lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_7205_,
                );
                lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7212_,
                );
                lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7213_,
                );
                lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7214_,
                );
                lean_inc(v_mvarId_7175_);
                v___x_7226_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_7175_,
                    v___x_7225_,
                    v___y_7178_,
                    v___y_7179_,
                    v___y_7180_,
                );
                lean_dec_ref_known(v___x_7225_, 7);
                if lean_obj_tag(v___x_7226_) == 0 {
                    v_a_7227_ = lean_ctor_get(v___x_7226_, 0);
                    lean_inc(v_a_7227_);
                    lean_dec_ref_known(v___x_7226_, 1);
                    v___x_7228_ = l_Lean_MVarId_propext___lam__0___closed__1;
                    v___x_7229_ = lean_unsigned_to_nat(3);
                    v___x_7230_ = l_Lean_Expr_isAppOfArity(v_a_7227_, v___x_7228_, v___x_7229_);
                    if v___x_7230_ == 0 {
                        lean_dec(v_a_7227_);
                        lean_dec(v_mvarId_7175_);
                        v___x_7231_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                        );
                        v___x_7232_ =
                            l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                v___x_7231_,
                                v___y_7177_,
                                v___y_7178_,
                                v___y_7179_,
                                v___y_7180_,
                            );
                        return v___x_7232_;
                    } else {
                        v___x_7233_ = l_Lean_Expr_appFn_x21(v_a_7227_);
                        v___x_7234_ = l_Lean_Expr_appArg_x21(v___x_7233_);
                        lean_dec_ref(v___x_7233_);
                        v___x_7235_ = l_Lean_Expr_appArg_x21(v_a_7227_);
                        lean_dec(v_a_7227_);
                        v___x_7236_ = l_Lean_MVarId_subsingletonElim___lam__0___closed__1;
                        v___x_7237_ = lean_unsigned_to_nat(2);
                        v___x_7238_ = lean_mk_empty_array_with_capacity(v___x_7237_);
                        v___x_7239_ = lean_array_push(v___x_7238_, v___x_7234_);
                        v___x_7240_ = lean_array_push(v___x_7239_, v___x_7235_);
                        v___x_7241_ = l_Lean_Meta_mkAppM(
                            v___x_7236_,
                            v___x_7240_,
                            v___y_7177_,
                            v___y_7178_,
                            v___y_7179_,
                            v___y_7180_,
                        );
                        if lean_obj_tag(v___x_7241_) == 0 {
                            v_a_7242_ = lean_ctor_get(v___x_7241_, 0);
                            lean_inc(v_a_7242_);
                            lean_dec_ref_known(v___x_7241_, 1);
                            v___x_7243_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                    v_mvarId_7175_,
                                    v_a_7242_,
                                    v___y_7178_,
                                );
                            v_isSharedCheck_7251_ = (!lean_is_exclusive(v___x_7243_)) as u8;
                            if v_isSharedCheck_7251_ == 0 {
                                v_unused_7252_ = lean_ctor_get(v___x_7243_, 0);
                                lean_dec(v_unused_7252_);
                                v___x_7245_ = v___x_7243_;
                                v_isShared_7246_ = v_isSharedCheck_7251_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_7243_);
                                v___x_7245_ = lean_box(0);
                                v_isShared_7246_ = v_isSharedCheck_7251_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarId_7175_);
                            v_a_7253_ = lean_ctor_get(v___x_7241_, 0);
                            v_isSharedCheck_7260_ = (!lean_is_exclusive(v___x_7241_)) as u8;
                            if v_isSharedCheck_7260_ == 0 {
                                v___x_7255_ = v___x_7241_;
                                v_isShared_7256_ = v_isSharedCheck_7260_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_7253_);
                                lean_dec(v___x_7241_);
                                v___x_7255_ = lean_box(0);
                                v_isShared_7256_ = v_isSharedCheck_7260_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_mvarId_7175_);
                    v_a_7261_ = lean_ctor_get(v___x_7226_, 0);
                    v_isSharedCheck_7268_ = (!lean_is_exclusive(v___x_7226_)) as u8;
                    if v_isSharedCheck_7268_ == 0 {
                        v___x_7263_ = v___x_7226_;
                        v_isShared_7264_ = v_isSharedCheck_7268_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_7261_);
                        lean_dec(v___x_7226_);
                        v___x_7263_ = lean_box(0);
                        v_isShared_7264_ = v_isSharedCheck_7268_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7247_ = lean_box((v___x_7230_) as usize);
                if v_isShared_7246_ == 0 {
                    lean_ctor_set(v___x_7245_, 0, v___x_7247_);
                    v___x_7249_ = v___x_7245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7250_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7250_, 0, v___x_7247_);
                    v___x_7249_ = v_reuseFailAlloc_7250_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7249_;
            }
            5 => {
                if v_isShared_7256_ == 0 {
                    v___x_7258_ = v___x_7255_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7259_, 0, v_a_7253_);
                    v___x_7258_ = v_reuseFailAlloc_7259_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7258_;
            }
            7 => {
                if v_isShared_7264_ == 0 {
                    v___x_7266_ = v___x_7263_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 0, v_a_7261_);
                    v___x_7266_ = v_reuseFailAlloc_7267_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7266_;
            }
            9 => {
                if v_isShared_7274_ == 0 {
                    v___x_7276_ = v___x_7273_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7277_, 0, v_a_7271_);
                    v___x_7276_ = v_reuseFailAlloc_7277_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_subsingletonElim___lam__0___boxed(
    mut v_mvarId_7279_: *mut LeanObject,
    mut v___x_7280_: *mut LeanObject,
    mut v___y_7281_: *mut LeanObject,
    mut v___y_7282_: *mut LeanObject,
    mut v___y_7283_: *mut LeanObject,
    mut v___y_7284_: *mut LeanObject,
    mut v___y_7285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7286_: *mut LeanObject = core::ptr::null_mut();
    v_res_7286_ = l_Lean_MVarId_subsingletonElim___lam__0(
        v_mvarId_7279_,
        v___x_7280_,
        v___y_7281_,
        v___y_7282_,
        v___y_7283_,
        v___y_7284_,
    );
    lean_dec(v___y_7284_);
    lean_dec_ref(v___y_7283_);
    lean_dec(v___y_7282_);
    lean_dec_ref(v___y_7281_);
    return v_res_7286_;
}
pub unsafe fn l_Lean_MVarId_subsingletonElim(
    mut v_mvarId_7290_: *mut LeanObject,
    mut v_a_7291_: *mut LeanObject,
    mut v_a_7292_: *mut LeanObject,
    mut v_a_7293_: *mut LeanObject,
    mut v_a_7294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    v___x_7296_ = l_Lean_MVarId_subsingletonElim___closed__1;
    lean_inc(v_mvarId_7290_);
    v___f_7297_ = lean_alloc_closure(
        l_Lean_MVarId_subsingletonElim___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_7297_, 0, v_mvarId_7290_);
    lean_closure_set(v___f_7297_, 1, v___x_7296_);
    v___f_7298_ = lean_alloc_closure(
        l_Lean_MVarId_proofIrrelHeq___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_7298_, 0, v___f_7297_);
    v___x_7299_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_7290_,
        v___f_7298_,
        v_a_7291_,
        v_a_7292_,
        v_a_7293_,
        v_a_7294_,
    );
    return v___x_7299_;
}
pub unsafe fn l_Lean_MVarId_subsingletonElim___boxed(
    mut v_mvarId_7300_: *mut LeanObject,
    mut v_a_7301_: *mut LeanObject,
    mut v_a_7302_: *mut LeanObject,
    mut v_a_7303_: *mut LeanObject,
    mut v_a_7304_: *mut LeanObject,
    mut v_a_7305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7306_: *mut LeanObject = core::ptr::null_mut();
    v_res_7306_ =
        l_Lean_MVarId_subsingletonElim(v_mvarId_7300_, v_a_7301_, v_a_7302_, v_a_7303_, v_a_7304_);
    lean_dec(v_a_7304_);
    lean_dec_ref(v_a_7303_);
    lean_dec(v_a_7302_);
    lean_dec_ref(v_a_7301_);
    return v_res_7306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Apply(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Apply(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Apply(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Apply(builtin);
}
