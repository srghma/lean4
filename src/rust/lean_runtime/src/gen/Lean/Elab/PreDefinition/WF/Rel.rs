// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: Lean.Meta.Tactic.Rename Lean.Elab.PreDefinition.TerminationMeasure Lean.Elab.PreDefinition.FixedParams Lean.Meta.ArgsPacker
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_replaceRef};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    initialize_Lean_Elab_PreDefinition_FixedParams, l_Lean_Elab_FixedParamPerm_instantiateForall,
    l_Lean_Elab_FixedParamPerm_instantiateLambda,
    runtime_initialize_Lean_Elab_PreDefinition_FixedParams,
};
use crate::r#gen::Lean::Elab::PreDefinition::TerminationMeasure::{
    initialize_Lean_Elab_PreDefinition_TerminationMeasure,
    l_Lean_Elab_instInhabitedTerminationMeasure_default,
    runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_instInhabitedTermElabM, l_Lean_Elab_Term_withDeclName___redArg,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
    l_Lean_mkApp4,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::ArgsPacker::{
    initialize_Lean_Meta_ArgsPacker, l_Lean_Meta_ArgsPacker_arities,
    l_Lean_Meta_ArgsPacker_uncurryND, runtime_initialize_Lean_Meta_ArgsPacker,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l_Lean_Meta_isExprDefEqGuarded,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Rename::{
    initialize_Lean_Meta_Tactic_Rename, runtime_initialize_Lean_Meta_Tactic_Rename,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_8, lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 87, 70, 46, 82, 101, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 87, 70, 46, 99, 104, 101, 99, 107, 67, 111, 100, 111, 109, 97, 105, 110, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 115, 46, 115, 105, 122, 101, 32, 61, 32, 97, 114, 105, 116, 121, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [84, 104, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32, 109, 101, 97, 115, 117, 114, 101, 39, 115, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 100, 101, 112, 101, 110, 100, 32, 111, 110, 32, 116, 104, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [102, 117, 110, 99, 116, 105, 111, 110, 39, 115, 32, 118, 97, 114, 121, 105, 110, 103, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 98, 117, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [39, 115, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32, 109, 101, 97, 115, 117, 114, 101, 32, 100, 111, 101, 115, 58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [84, 114, 121, 32, 117, 115, 105, 110, 103, 32, 96, 115, 105, 122, 101, 79, 102, 96, 32, 101, 120, 112, 108, 105, 99, 105, 116, 108, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__12_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [84, 104, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32, 109, 101, 97, 115, 117, 114, 101, 115, 32, 111, 102, 32, 109, 117, 116, 117, 97, 108, 108, 121, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2_value: LeanStringObject<64> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32, 109, 101, 97, 115, 117, 114, 101, 32, 111, 102, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [119, 104, 105, 108, 101, 32, 116, 104, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32, 109, 101, 97, 115, 117, 114, 101, 32, 111, 102, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_WF_checkCodomains___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_WF_checkCodomains___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_checkCodomains___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_checkCodomains___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Elab_WF_checkCodomains___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_checkCodomains___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            87, 101, 108, 108, 70, 111, 117, 110, 100, 101, 100, 82, 101, 108, 97, 116, 105, 111,
            110, 0,
        ],
    };
static mut l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
            3429923986742416119 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value: LeanStringObject<9> =
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
        m_data: [105, 110, 118, 73, 109, 97, 103, 101, 0],
    };
static mut l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__2_value)
                as *mut LeanObject,
            3221764316860498547 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3_value)
        as *mut LeanObject;
pub unsafe fn _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    v___x_1211_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
    return v___x_1211_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(
    mut v_msg_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826__overap_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___closed__0,
    );
    v___x_6826__overap_1221_ = lean_panic_fn_borrowed(v___x_1220_, v_msg_1212_);
    lean_inc(v___y_1218_);
    lean_inc_ref(v___y_1217_);
    lean_inc(v___y_1216_);
    lean_inc_ref(v___y_1215_);
    lean_inc(v___y_1214_);
    lean_inc_ref(v___y_1213_);
    v___x_1222_ = lean_apply_7(
        v___x_6826__overap_1221_,
        v___y_1213_,
        v___y_1214_,
        v___y_1215_,
        v___y_1216_,
        v___y_1217_,
        v___y_1218_,
        lean_box(0),
    );
    return v___x_1222_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0___boxed(
    mut v_msg_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1231_: *mut LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(
        v_msg_1223_,
        v___y_1224_,
        v___y_1225_,
        v___y_1226_,
        v___y_1227_,
        v___y_1228_,
        v___y_1229_,
    );
    lean_dec(v___y_1229_);
    lean_dec_ref(v___y_1228_);
    lean_dec(v___y_1227_);
    lean_dec_ref(v___y_1226_);
    lean_dec(v___y_1225_);
    lean_dec_ref(v___y_1224_);
    return v_res_1231_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(
    mut v_k_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v_b_1235_: *mut LeanObject,
    mut v_c_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1240_);
    lean_inc_ref(v___y_1239_);
    lean_inc(v___y_1238_);
    lean_inc_ref(v___y_1237_);
    lean_inc(v___y_1234_);
    lean_inc_ref(v___y_1233_);
    v___x_1242_ = lean_apply_9(
        v_k_1232_,
        v_b_1235_,
        v_c_1236_,
        v___y_1233_,
        v___y_1234_,
        v___y_1237_,
        v___y_1238_,
        v___y_1239_,
        v___y_1240_,
        lean_box(0),
    );
    return v___x_1242_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed(
    mut v_k_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v_b_1246_: *mut LeanObject,
    mut v_c_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1253_: *mut LeanObject = core::ptr::null_mut();
    v_res_1253_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0(v_k_1243_, v___y_1244_, v___y_1245_, v_b_1246_, v_c_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
    lean_dec(v___y_1251_);
    lean_dec_ref(v___y_1250_);
    lean_dec(v___y_1249_);
    lean_dec_ref(v___y_1248_);
    lean_dec(v___y_1245_);
    lean_dec_ref(v___y_1244_);
    return v_res_1253_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(
    mut v_type_1254_: *mut LeanObject,
    mut v_maxFVars_x3f_1255_: *mut LeanObject,
    mut v_k_1256_: *mut LeanObject,
    mut v_cleanupAnnotations_1257_: u8,
    mut v_whnfType_1258_: u8,
    mut v___y_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1260_);
                lean_inc_ref(v___y_1259_);
                v___f_1266_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_1266_, 0, v_k_1256_);
                lean_closure_set(v___f_1266_, 1, v___y_1259_);
                lean_closure_set(v___f_1266_, 2, v___y_1260_);
                v___x_1267_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_1254_,
                    v_maxFVars_x3f_1255_,
                    v___f_1266_,
                    v_cleanupAnnotations_1257_,
                    v_whnfType_1258_,
                    v___y_1261_,
                    v___y_1262_,
                    v___y_1263_,
                    v___y_1264_,
                );
                if lean_obj_tag(v___x_1267_) == 0 {
                    return v___x_1267_;
                } else {
                    v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
                    v_isSharedCheck_1275_ = (!lean_is_exclusive(v___x_1267_)) as u8;
                    if v_isSharedCheck_1275_ == 0 {
                        v___x_1270_ = v___x_1267_;
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1268_);
                        lean_dec(v___x_1267_);
                        v___x_1270_ = lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1271_ == 0 {
                    v___x_1273_ = v___x_1270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg___boxed(
    mut v_type_1276_: *mut LeanObject,
    mut v_maxFVars_x3f_1277_: *mut LeanObject,
    mut v_k_1278_: *mut LeanObject,
    mut v_cleanupAnnotations_1279_: *mut LeanObject,
    mut v_whnfType_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1288_: u8 = 0;
    let mut v_whnfType_boxed_1289_: u8 = 0;
    let mut v_res_1290_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1288_ = (lean_unbox(v_cleanupAnnotations_1279_) as u8);
    v_whnfType_boxed_1289_ = (lean_unbox(v_whnfType_1280_) as u8);
    v_res_1290_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(
            v_type_1276_,
            v_maxFVars_x3f_1277_,
            v_k_1278_,
            v_cleanupAnnotations_boxed_1288_,
            v_whnfType_boxed_1289_,
            v___y_1281_,
            v___y_1282_,
            v___y_1283_,
            v___y_1284_,
            v___y_1285_,
            v___y_1286_,
        );
    lean_dec(v___y_1286_);
    lean_dec_ref(v___y_1285_);
    lean_dec(v___y_1284_);
    lean_dec_ref(v___y_1283_);
    lean_dec(v___y_1282_);
    lean_dec_ref(v___y_1281_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(
    mut v_00_u03b1_1291_: *mut LeanObject,
    mut v_type_1292_: *mut LeanObject,
    mut v_maxFVars_x3f_1293_: *mut LeanObject,
    mut v_k_1294_: *mut LeanObject,
    mut v_cleanupAnnotations_1295_: u8,
    mut v_whnfType_1296_: u8,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v___x_1304_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(
            v_type_1292_,
            v_maxFVars_x3f_1293_,
            v_k_1294_,
            v_cleanupAnnotations_1295_,
            v_whnfType_1296_,
            v___y_1297_,
            v___y_1298_,
            v___y_1299_,
            v___y_1300_,
            v___y_1301_,
            v___y_1302_,
        );
    return v___x_1304_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___boxed(
    mut v_00_u03b1_1305_: *mut LeanObject,
    mut v_type_1306_: *mut LeanObject,
    mut v_maxFVars_x3f_1307_: *mut LeanObject,
    mut v_k_1308_: *mut LeanObject,
    mut v_cleanupAnnotations_1309_: *mut LeanObject,
    mut v_whnfType_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1318_: u8 = 0;
    let mut v_whnfType_boxed_1319_: u8 = 0;
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1318_ = (lean_unbox(v_cleanupAnnotations_1309_) as u8);
    v_whnfType_boxed_1319_ = (lean_unbox(v_whnfType_1310_) as u8);
    v_res_1320_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5(
        v_00_u03b1_1305_,
        v_type_1306_,
        v_maxFVars_x3f_1307_,
        v_k_1308_,
        v_cleanupAnnotations_boxed_1318_,
        v_whnfType_boxed_1319_,
        v___y_1311_,
        v___y_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
    );
    lean_dec(v___y_1316_);
    lean_dec_ref(v___y_1315_);
    lean_dec(v___y_1314_);
    lean_dec_ref(v___y_1313_);
    lean_dec(v___y_1312_);
    lean_dec_ref(v___y_1311_);
    return v_res_1320_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(
    mut v_a_1321_: *mut LeanObject,
    mut v_as_1322_: *mut LeanObject,
    mut v_i_1323_: usize,
    mut v_stop_1324_: usize,
) -> u8 {
    let mut v___x_1325_: u8 = 0;
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: usize = 0;
    let mut v___x_1329_: usize = 0;
    let mut v___x_1331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1325_ = lean_usize_dec_eq(v_i_1323_, v_stop_1324_);
                if v___x_1325_ == 0 {
                    v___x_1326_ = lean_array_uget_borrowed(v_as_1322_, v_i_1323_);
                    v___x_1327_ = l_Lean_instBEqFVarId_beq(v_a_1321_, v___x_1326_);
                    if v___x_1327_ == 0 {
                        v___x_1328_ = 1usize;
                        v___x_1329_ = lean_usize_add(v_i_1323_, v___x_1328_);
                        v_i_1323_ = v___x_1329_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1327_;
                    }
                } else {
                    v___x_1331_ = 0;
                    return v___x_1331_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2___boxed(
    mut v_a_1332_: *mut LeanObject,
    mut v_as_1333_: *mut LeanObject,
    mut v_i_1334_: *mut LeanObject,
    mut v_stop_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1336_: usize = 0;
    let mut v_stop_boxed_1337_: usize = 0;
    let mut v_res_1338_: u8 = 0;
    let mut v_r_1339_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1336_ = lean_unbox_usize(v_i_1334_);
    lean_dec(v_i_1334_);
    v_stop_boxed_1337_ = lean_unbox_usize(v_stop_1335_);
    lean_dec(v_stop_1335_);
    v_res_1338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_1332_, v_as_1333_, v_i_boxed_1336_, v_stop_boxed_1337_);
    lean_dec_ref(v_as_1333_);
    lean_dec(v_a_1332_);
    v_r_1339_ = lean_box((v_res_1338_) as usize);
    return v_r_1339_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(
    mut v_as_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
) -> u8 {
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: u8 = 0;
    v___x_1342_ = lean_unsigned_to_nat(0);
    v___x_1343_ = lean_array_get_size(v_as_1340_);
    v___x_1344_ = lean_nat_dec_lt(v___x_1342_, v___x_1343_);
    if v___x_1344_ == 0 {
        return v___x_1344_;
    } else {
        if v___x_1344_ == 0 {
            return v___x_1344_;
        } else {
            let mut v___x_1345_: usize = 0;
            let mut v___x_1346_: usize = 0;
            let mut v___x_1347_: u8 = 0;
            v___x_1345_ = 0usize;
            v___x_1346_ = lean_usize_of_nat(v___x_1343_);
            v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2_spec__2(v_a_1341_, v_as_1340_, v___x_1345_, v___x_1346_);
            return v___x_1347_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2___boxed(
    mut v_as_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1350_: u8 = 0;
    let mut v_r_1351_: *mut LeanObject = core::ptr::null_mut();
    v_res_1350_ =
        l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(v_as_1348_, v_a_1349_);
    lean_dec(v_a_1349_);
    lean_dec_ref(v_as_1348_);
    v_r_1351_ = lean_box((v_res_1350_) as usize);
    return v_r_1351_;
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(
    mut v___x_1352_: *mut LeanObject,
    mut v_e_1353_: *mut LeanObject,
) -> u8 {
    let mut v___x_1354_: u8 = 0;
    let mut v_d_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v_binderType_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v_fn_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v_struct_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = l_Lean_Expr_hasFVar(v_e_1353_);
                if v___x_1354_ == 0 {
                    return v___x_1354_;
                } else {
                    match lean_obj_tag(v_e_1353_) {
                        7 => {
                            v_binderType_1360_ = lean_ctor_get(v_e_1353_, 1);
                            v_body_1361_ = lean_ctor_get(v_e_1353_, 2);
                            v_d_1356_ = v_binderType_1360_;
                            v_b_1357_ = v_body_1361_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_1362_ = lean_ctor_get(v_e_1353_, 1);
                            v_body_1363_ = lean_ctor_get(v_e_1353_, 2);
                            v_d_1356_ = v_binderType_1362_;
                            v_b_1357_ = v_body_1363_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_1364_ = lean_ctor_get(v_e_1353_, 1);
                            v_e_1353_ = v_expr_1364_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_1366_ = lean_ctor_get(v_e_1353_, 1);
                            v_value_1367_ = lean_ctor_get(v_e_1353_, 2);
                            v_body_1368_ = lean_ctor_get(v_e_1353_, 3);
                            v___x_1369_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_1352_, v_type_1366_);
                            if v___x_1369_ == 0 {
                                v___x_1370_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_1352_, v_value_1367_);
                                if v___x_1370_ == 0 {
                                    v_e_1353_ = v_body_1368_;
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_1354_;
                                }
                            } else {
                                return v___x_1354_;
                            }
                        }
                        5 => {
                            v_fn_1372_ = lean_ctor_get(v_e_1353_, 0);
                            v_arg_1373_ = lean_ctor_get(v_e_1353_, 1);
                            v___x_1374_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_1352_, v_fn_1372_);
                            if v___x_1374_ == 0 {
                                v_e_1353_ = v_arg_1373_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_1354_;
                            }
                        }
                        11 => {
                            v_struct_1376_ = lean_ctor_get(v_e_1353_, 2);
                            v_e_1353_ = v_struct_1376_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_fvarId_1378_ = lean_ctor_get(v_e_1353_, 0);
                            v___x_1379_ =
                                l_Array_contains___at___00Lean_Elab_WF_checkCodomains_spec__2(
                                    v___x_1352_,
                                    v_fvarId_1378_,
                                );
                            return v___x_1379_;
                        }
                        _ => {
                            v___x_1380_ = 0;
                            return v___x_1380_;
                        }
                    }
                }
            }
            1 => {
                v___x_1358_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_1352_, v_d_1356_);
                if v___x_1358_ == 0 {
                    v_e_1353_ = v_b_1357_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1354_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3___boxed(
    mut v___x_1381_: *mut LeanObject,
    mut v_e_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1383_: u8 = 0;
    let mut v_r_1384_: *mut LeanObject = core::ptr::null_mut();
    v_res_1383_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_1381_, v_e_1382_);
    lean_dec_ref(v_e_1382_);
    lean_dec_ref(v___x_1381_);
    v_r_1384_ = lean_box((v_res_1383_) as usize);
    return v_r_1384_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(
    mut v_sz_1385_: usize,
    mut v_i_1386_: usize,
    mut v_bs_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: u8 = 0;
    let mut v_v_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: usize = 0;
    let mut v___x_1394_: usize = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1388_ = lean_usize_dec_lt(v_i_1386_, v_sz_1385_);
                if v___x_1388_ == 0 {
                    return v_bs_1387_;
                } else {
                    v_v_1389_ = lean_array_uget(v_bs_1387_, v_i_1386_);
                    v___x_1390_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1391_ = lean_array_uset(v_bs_1387_, v_i_1386_, v___x_1390_);
                    v___x_1392_ = l_Lean_Expr_fvarId_x21(v_v_1389_);
                    lean_dec(v_v_1389_);
                    v___x_1393_ = 1usize;
                    v___x_1394_ = lean_usize_add(v_i_1386_, v___x_1393_);
                    v___x_1395_ = lean_array_uset(v_bs_x27_1391_, v_i_1386_, v___x_1392_);
                    v_i_1386_ = v___x_1394_;
                    v_bs_1387_ = v___x_1395_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1___boxed(
    mut v_sz_1397_: *mut LeanObject,
    mut v_i_1398_: *mut LeanObject,
    mut v_bs_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1400_: usize = 0;
    let mut v_i_boxed_1401_: usize = 0;
    let mut v_res_1402_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1397_);
    lean_dec(v_sz_1397_);
    v_i_boxed_1401_ = lean_unbox_usize(v_i_1398_);
    lean_dec(v_i_1398_);
    v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_boxed_1400_, v_i_boxed_1401_, v_bs_1399_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(
    mut v_msgData_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
    mut v___y_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1409_ = lean_st_ref_get(v___y_1407_);
    v_env_1410_ = lean_ctor_get(v___x_1409_, 0);
    lean_inc_ref(v_env_1410_);
    lean_dec(v___x_1409_);
    v___x_1411_ = lean_st_ref_get(v___y_1405_);
    v_mctx_1412_ = lean_ctor_get(v___x_1411_, 0);
    lean_inc_ref(v_mctx_1412_);
    lean_dec(v___x_1411_);
    v_lctx_1413_ = lean_ctor_get(v___y_1404_, 2);
    v_options_1414_ = lean_ctor_get(v___y_1406_, 2);
    lean_inc_ref(v_options_1414_);
    lean_inc_ref(v_lctx_1413_);
    v___x_1415_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1415_, 0, v_env_1410_);
    lean_ctor_set(v___x_1415_, 1, v_mctx_1412_);
    lean_ctor_set(v___x_1415_, 2, v_lctx_1413_);
    lean_ctor_set(v___x_1415_, 3, v_options_1414_);
    v___x_1416_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1416_, 0, v___x_1415_);
    lean_ctor_set(v___x_1416_, 1, v_msgData_1403_);
    v___x_1417_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1417_, 0, v___x_1416_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7___boxed(
    mut v_msgData_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1424_: *mut LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msgData_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
    lean_dec(v___y_1422_);
    lean_dec_ref(v___y_1421_);
    lean_dec(v___y_1420_);
    lean_dec_ref(v___y_1419_);
    return v_res_1424_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(
    mut v_opts_1425_: *mut LeanObject,
    mut v_opt_1426_: *mut LeanObject,
) -> u8 {
    let mut v_name_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v_name_1427_ = lean_ctor_get(v_opt_1426_, 0);
    v_defValue_1428_ = lean_ctor_get(v_opt_1426_, 1);
    v_map_1429_ = lean_ctor_get(v_opts_1425_, 0);
    v___x_1430_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1429_,
            v_name_1427_,
        );
    if lean_obj_tag(v___x_1430_) == 0 {
        let mut v___x_1431_: u8 = 0;
        v___x_1431_ = (lean_unbox(v_defValue_1428_) as u8);
        return v___x_1431_;
    } else {
        let mut v_val_1432_: *mut LeanObject = core::ptr::null_mut();
        v_val_1432_ = lean_ctor_get(v___x_1430_, 0);
        lean_inc(v_val_1432_);
        lean_dec_ref_known(v___x_1430_, 1);
        if lean_obj_tag(v_val_1432_) == 1 {
            let mut v_v_1433_: u8 = 0;
            v_v_1433_ = lean_ctor_get_uint8(v_val_1432_, 0 as u32);
            lean_dec_ref_known(v_val_1432_, 0);
            return v_v_1433_;
        } else {
            let mut v___x_1434_: u8 = 0;
            lean_dec(v_val_1432_);
            v___x_1434_ = (lean_unbox(v_defValue_1428_) as u8);
            return v___x_1434_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11___boxed(
    mut v_opts_1435_: *mut LeanObject,
    mut v_opt_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1437_: u8 = 0;
    let mut v_r_1438_: *mut LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_opts_1435_, v_opt_1436_);
    lean_dec_ref(v_opt_1436_);
    lean_dec_ref(v_opts_1435_);
    v_r_1438_ = lean_box((v_res_1437_) as usize);
    return v_r_1438_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0()
-> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = lean_box(1);
    v___x_1440_ = l_Lean_MessageData_ofFormat(v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3()
-> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    v___x_1444_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__2;
    v___x_1445_ = l_Lean_MessageData_ofFormat(v___x_1444_);
    return v___x_1445_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(
    mut v_x_1446_: *mut LeanObject,
    mut v_x_1447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v_before_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut v_unused_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1447_) == 0 {
                    return v_x_1446_;
                } else {
                    v_head_1448_ = lean_ctor_get(v_x_1447_, 0);
                    v_tail_1449_ = lean_ctor_get(v_x_1447_, 1);
                    v_isSharedCheck_1471_ = (!lean_is_exclusive(v_x_1447_)) as u8;
                    if v_isSharedCheck_1471_ == 0 {
                        v___x_1451_ = v_x_1447_;
                        v_isShared_1452_ = v_isSharedCheck_1471_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1449_);
                        lean_inc(v_head_1448_);
                        lean_dec(v_x_1447_);
                        v___x_1451_ = lean_box(0);
                        v_isShared_1452_ = v_isSharedCheck_1471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1453_ = lean_ctor_get(v_head_1448_, 0);
                v_isSharedCheck_1469_ = (!lean_is_exclusive(v_head_1448_)) as u8;
                if v_isSharedCheck_1469_ == 0 {
                    v_unused_1470_ = lean_ctor_get(v_head_1448_, 1);
                    lean_dec(v_unused_1470_);
                    v___x_1455_ = v_head_1448_;
                    v_isShared_1456_ = v_isSharedCheck_1469_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_1453_);
                    lean_dec(v_head_1448_);
                    v___x_1455_ = lean_box(0);
                    v_isShared_1456_ = v_isSharedCheck_1469_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1457_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
                if v_isShared_1456_ == 0 {
                    lean_ctor_set_tag(v___x_1455_, 7);
                    lean_ctor_set(v___x_1455_, 1, v___x_1457_);
                    lean_ctor_set(v___x_1455_, 0, v_x_1446_);
                    v___x_1459_ = v___x_1455_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1468_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_x_1446_);
                    lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1457_);
                    v___x_1459_ = v_reuseFailAlloc_1468_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1460_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__3);
                if v_isShared_1452_ == 0 {
                    lean_ctor_set_tag(v___x_1451_, 7);
                    lean_ctor_set(v___x_1451_, 1, v___x_1460_);
                    lean_ctor_set(v___x_1451_, 0, v___x_1459_);
                    v___x_1462_ = v___x_1451_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1459_);
                    lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1460_);
                    v___x_1462_ = v_reuseFailAlloc_1467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1463_ = l_Lean_MessageData_ofSyntax(v_before_1453_);
                v___x_1464_ = l_Lean_indentD(v___x_1463_);
                v___x_1465_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1465_, 0, v___x_1462_);
                lean_ctor_set(v___x_1465_, 1, v___x_1464_);
                v_x_1446_ = v___x_1465_;
                v_x_1447_ = v_tail_1449_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    v___x_1475_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__1;
    v___x_1476_ = l_Lean_MessageData_ofFormat(v___x_1475_);
    return v___x_1476_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(
    mut v_msgData_1477_: *mut LeanObject,
    mut v_macroStack_1478_: *mut LeanObject,
    mut v___y_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_unused_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1481_ = lean_ctor_get(v___y_1479_, 2);
                v___x_1482_ = l_Lean_Elab_pp_macroStack;
                v___x_1483_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__11(v_options_1481_, v___x_1482_);
                if v___x_1483_ == 0 {
                    lean_dec(v_macroStack_1478_);
                    v___x_1484_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1484_, 0, v_msgData_1477_);
                    return v___x_1484_;
                } else {
                    if lean_obj_tag(v_macroStack_1478_) == 0 {
                        v___x_1485_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1485_, 0, v_msgData_1477_);
                        return v___x_1485_;
                    } else {
                        v_head_1486_ = lean_ctor_get(v_macroStack_1478_, 0);
                        lean_inc(v_head_1486_);
                        v_after_1487_ = lean_ctor_get(v_head_1486_, 1);
                        v_isSharedCheck_1502_ = (!lean_is_exclusive(v_head_1486_)) as u8;
                        if v_isSharedCheck_1502_ == 0 {
                            v_unused_1503_ = lean_ctor_get(v_head_1486_, 0);
                            lean_dec(v_unused_1503_);
                            v___x_1489_ = v_head_1486_;
                            v_isShared_1490_ = v_isSharedCheck_1502_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_1487_);
                            lean_dec(v_head_1486_);
                            v___x_1489_ = lean_box(0);
                            v_isShared_1490_ = v_isSharedCheck_1502_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1491_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12___closed__0);
                if v_isShared_1490_ == 0 {
                    lean_ctor_set_tag(v___x_1489_, 7);
                    lean_ctor_set(v___x_1489_, 1, v___x_1491_);
                    lean_ctor_set(v___x_1489_, 0, v_msgData_1477_);
                    v___x_1493_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_msgData_1477_);
                    lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1491_);
                    v___x_1493_ = v_reuseFailAlloc_1501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1494_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___closed__2);
                v___x_1495_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1495_, 0, v___x_1493_);
                lean_ctor_set(v___x_1495_, 1, v___x_1494_);
                v___x_1496_ = l_Lean_MessageData_ofSyntax(v_after_1487_);
                v___x_1497_ = l_Lean_indentD(v___x_1496_);
                v_msgData_1498_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_1498_, 0, v___x_1495_);
                lean_ctor_set(v_msgData_1498_, 1, v___x_1497_);
                v___x_1499_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8_spec__12(v_msgData_1498_, v_macroStack_1478_);
                v___x_1500_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1500_, 0, v___x_1499_);
                return v___x_1500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg___boxed(
    mut v_msgData_1504_: *mut LeanObject,
    mut v_macroStack_1505_: *mut LeanObject,
    mut v___y_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_1504_, v_macroStack_1505_, v___y_1506_);
    lean_dec_ref(v___y_1506_);
    return v_res_1508_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(
    mut v_msg_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
    mut v___y_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1517_ = lean_ctor_get(v___y_1514_, 5);
                v___x_1518_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__7(v_msg_1509_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
                v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
                lean_inc(v_a_1519_);
                lean_dec_ref(v___x_1518_);
                v_macroStack_1520_ = lean_ctor_get(v___y_1510_, 1);
                v___x_1521_ = l_Lean_Elab_getBetterRef(v_ref_1517_, v_macroStack_1520_);
                lean_inc(v_macroStack_1520_);
                v___x_1522_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_a_1519_, v_macroStack_1520_, v___y_1514_);
                v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
                v_isSharedCheck_1531_ = (!lean_is_exclusive(v___x_1522_)) as u8;
                if v_isSharedCheck_1531_ == 0 {
                    v___x_1525_ = v___x_1522_;
                    v_isShared_1526_ = v_isSharedCheck_1531_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1523_);
                    lean_dec(v___x_1522_);
                    v___x_1525_ = lean_box(0);
                    v_isShared_1526_ = v_isSharedCheck_1531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1527_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1527_, 0, v___x_1521_);
                lean_ctor_set(v___x_1527_, 1, v_a_1523_);
                if v_isShared_1526_ == 0 {
                    lean_ctor_set_tag(v___x_1525_, 1);
                    lean_ctor_set(v___x_1525_, 0, v___x_1527_);
                    v___x_1529_ = v___x_1525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg___boxed(
    mut v_msg_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1540_: *mut LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
    lean_dec(v___y_1538_);
    lean_dec_ref(v___y_1537_);
    lean_dec(v___y_1536_);
    lean_dec_ref(v___y_1535_);
    lean_dec(v___y_1534_);
    lean_dec_ref(v___y_1533_);
    return v_res_1540_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(
    mut v_ref_1541_: *mut LeanObject,
    mut v_msg_1542_: *mut LeanObject,
    mut v___y_1543_: *mut LeanObject,
    mut v___y_1544_: *mut LeanObject,
    mut v___y_1545_: *mut LeanObject,
    mut v___y_1546_: *mut LeanObject,
    mut v___y_1547_: *mut LeanObject,
    mut v___y_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1562_: u8 = 0;
    let mut v_cancelTk_x3f_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1564_: u8 = 0;
    let mut v_inheritedTraceOptions_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1550_ = lean_ctor_get(v___y_1547_, 0);
    v_fileMap_1551_ = lean_ctor_get(v___y_1547_, 1);
    v_options_1552_ = lean_ctor_get(v___y_1547_, 2);
    v_currRecDepth_1553_ = lean_ctor_get(v___y_1547_, 3);
    v_maxRecDepth_1554_ = lean_ctor_get(v___y_1547_, 4);
    v_ref_1555_ = lean_ctor_get(v___y_1547_, 5);
    v_currNamespace_1556_ = lean_ctor_get(v___y_1547_, 6);
    v_openDecls_1557_ = lean_ctor_get(v___y_1547_, 7);
    v_initHeartbeats_1558_ = lean_ctor_get(v___y_1547_, 8);
    v_maxHeartbeats_1559_ = lean_ctor_get(v___y_1547_, 9);
    v_quotContext_1560_ = lean_ctor_get(v___y_1547_, 10);
    v_currMacroScope_1561_ = lean_ctor_get(v___y_1547_, 11);
    v_diag_1562_ = lean_ctor_get_uint8(
        v___y_1547_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1563_ = lean_ctor_get(v___y_1547_, 12);
    v_suppressElabErrors_1564_ = lean_ctor_get_uint8(
        v___y_1547_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1565_ = lean_ctor_get(v___y_1547_, 13);
    v_ref_1566_ = l_Lean_replaceRef(v_ref_1541_, v_ref_1555_);
    lean_inc_ref(v_inheritedTraceOptions_1565_);
    lean_inc(v_cancelTk_x3f_1563_);
    lean_inc(v_currMacroScope_1561_);
    lean_inc(v_quotContext_1560_);
    lean_inc(v_maxHeartbeats_1559_);
    lean_inc(v_initHeartbeats_1558_);
    lean_inc(v_openDecls_1557_);
    lean_inc(v_currNamespace_1556_);
    lean_inc(v_maxRecDepth_1554_);
    lean_inc(v_currRecDepth_1553_);
    lean_inc_ref(v_options_1552_);
    lean_inc_ref(v_fileMap_1551_);
    lean_inc_ref(v_fileName_1550_);
    v___x_1567_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1567_, 0, v_fileName_1550_);
    lean_ctor_set(v___x_1567_, 1, v_fileMap_1551_);
    lean_ctor_set(v___x_1567_, 2, v_options_1552_);
    lean_ctor_set(v___x_1567_, 3, v_currRecDepth_1553_);
    lean_ctor_set(v___x_1567_, 4, v_maxRecDepth_1554_);
    lean_ctor_set(v___x_1567_, 5, v_ref_1566_);
    lean_ctor_set(v___x_1567_, 6, v_currNamespace_1556_);
    lean_ctor_set(v___x_1567_, 7, v_openDecls_1557_);
    lean_ctor_set(v___x_1567_, 8, v_initHeartbeats_1558_);
    lean_ctor_set(v___x_1567_, 9, v_maxHeartbeats_1559_);
    lean_ctor_set(v___x_1567_, 10, v_quotContext_1560_);
    lean_ctor_set(v___x_1567_, 11, v_currMacroScope_1561_);
    lean_ctor_set(v___x_1567_, 12, v_cancelTk_x3f_1563_);
    lean_ctor_set(v___x_1567_, 13, v_inheritedTraceOptions_1565_);
    lean_ctor_set_uint8(
        v___x_1567_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1562_,
    );
    lean_ctor_set_uint8(
        v___x_1567_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1564_,
    );
    v___x_1568_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___x_1567_, v___y_1548_);
    lean_dec_ref_known(v___x_1567_, 14);
    return v___x_1568_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg___boxed(
    mut v_ref_1569_: *mut LeanObject,
    mut v_msg_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(
        v_ref_1569_,
        v_msg_1570_,
        v___y_1571_,
        v___y_1572_,
        v___y_1573_,
        v___y_1574_,
        v___y_1575_,
        v___y_1576_,
    );
    lean_dec(v___y_1576_);
    lean_dec_ref(v___y_1575_);
    lean_dec(v___y_1574_);
    lean_dec_ref(v___y_1573_);
    lean_dec(v___y_1572_);
    lean_dec_ref(v___y_1571_);
    lean_dec(v_ref_1569_);
    return v_res_1578_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__2;
    v___x_1583_ = lean_unsigned_to_nat(6);
    v___x_1584_ = lean_unsigned_to_nat(33);
    v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__1;
    v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__0;
    v___x_1587_ = l_mkPanicMessageWithDecl(
        v___x_1586_,
        v___x_1585_,
        v___x_1584_,
        v___x_1583_,
        v___x_1582_,
    );
    return v___x_1587_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__4;
    v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__6;
    v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
    return v___x_1593_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__8;
    v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
    return v___x_1596_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__10;
    v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14()
-> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__13;
    v___x_1604_ = l_Lean_MessageData_ofFormat(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(
    mut v___x_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_ref_1608_: *mut LeanObject,
    mut v_xs_1609_: *mut LeanObject,
    mut v_codomain_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1622_: usize = 0;
    let mut v___x_1623_: usize = 0;
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v_unused_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1618_ = lean_array_get_size(v_xs_1609_);
                v___x_1619_ = lean_nat_dec_eq(v___x_1618_, v___x_1605_);
                if v___x_1619_ == 0 {
                    lean_dec_ref(v_codomain_1610_);
                    lean_dec_ref(v_xs_1609_);
                    lean_dec_ref(v_a_1607_);
                    lean_dec(v_a_1606_);
                    v___x_1620_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__3);
                    v___x_1621_ = l_panic___at___00Lean_Elab_WF_checkCodomains_spec__0(
                        v___x_1620_,
                        v___y_1611_,
                        v___y_1612_,
                        v___y_1613_,
                        v___y_1614_,
                        v___y_1615_,
                        v___y_1616_,
                    );
                    return v___x_1621_;
                } else {
                    v_sz_1622_ = lean_array_size(v_xs_1609_);
                    v___x_1623_ = 0usize;
                    v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_checkCodomains_spec__1(v_sz_1622_, v___x_1623_, v_xs_1609_);
                    v___x_1625_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Elab_WF_checkCodomains_spec__3(v___x_1624_, v_codomain_1610_);
                    lean_dec_ref(v___x_1624_);
                    if v___x_1625_ == 0 {
                        lean_dec_ref(v_a_1607_);
                        lean_dec(v_a_1606_);
                        v___x_1626_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1626_, 0, v_codomain_1610_);
                        return v___x_1626_;
                    } else {
                        v___x_1627_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__5);
                        v___x_1628_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__7);
                        v___x_1629_ = l_Lean_MessageData_ofName(v_a_1606_);
                        v___x_1630_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1630_, 0, v___x_1628_);
                        lean_ctor_set(v___x_1630_, 1, v___x_1629_);
                        v___x_1631_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__9);
                        v___x_1632_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1632_, 0, v___x_1630_);
                        lean_ctor_set(v___x_1632_, 1, v___x_1631_);
                        v___x_1633_ = l_Lean_indentExpr(v_a_1607_);
                        v___x_1634_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                        lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                        v___x_1635_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
                        v___x_1636_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1636_, 0, v___x_1634_);
                        lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                        v___x_1637_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1637_, 0, v___x_1627_);
                        lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                        v___x_1638_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
                        v___x_1639_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1639_, 0, v___x_1637_);
                        lean_ctor_set(v___x_1639_, 1, v___x_1638_);
                        v___x_1640_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_1608_, v___x_1639_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
                        if lean_obj_tag(v___x_1640_) == 0 {
                            v_isSharedCheck_1647_ = (!lean_is_exclusive(v___x_1640_)) as u8;
                            if v_isSharedCheck_1647_ == 0 {
                                v_unused_1648_ = lean_ctor_get(v___x_1640_, 0);
                                lean_dec(v_unused_1648_);
                                v___x_1642_ = v___x_1640_;
                                v_isShared_1643_ = v_isSharedCheck_1647_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_1640_);
                                v___x_1642_ = lean_box(0);
                                v_isShared_1643_ = v_isSharedCheck_1647_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_codomain_1610_);
                            v_a_1649_ = lean_ctor_get(v___x_1640_, 0);
                            v_isSharedCheck_1656_ = (!lean_is_exclusive(v___x_1640_)) as u8;
                            if v_isSharedCheck_1656_ == 0 {
                                v___x_1651_ = v___x_1640_;
                                v_isShared_1652_ = v_isSharedCheck_1656_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1649_);
                                lean_dec(v___x_1640_);
                                v___x_1651_ = lean_box(0);
                                v_isShared_1652_ = v_isSharedCheck_1656_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1643_ == 0 {
                    lean_ctor_set(v___x_1642_, 0, v_codomain_1610_);
                    v___x_1645_ = v___x_1642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_codomain_1610_);
                    v___x_1645_ = v_reuseFailAlloc_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1645_;
            }
            3 => {
                if v_isShared_1652_ == 0 {
                    v___x_1654_ = v___x_1651_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
                    v___x_1654_ = v_reuseFailAlloc_1655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed(
    mut v___x_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
    mut v_a_1659_: *mut LeanObject,
    mut v_ref_1660_: *mut LeanObject,
    mut v_xs_1661_: *mut LeanObject,
    mut v_codomain_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1670_: *mut LeanObject = core::ptr::null_mut();
    v_res_1670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0(v___x_1657_, v_a_1658_, v_a_1659_, v_ref_1660_, v_xs_1661_, v_codomain_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
    lean_dec(v___y_1668_);
    lean_dec_ref(v___y_1667_);
    lean_dec(v___y_1666_);
    lean_dec_ref(v___y_1665_);
    lean_dec(v___y_1664_);
    lean_dec_ref(v___y_1663_);
    lean_dec(v_ref_1660_);
    lean_dec(v___x_1657_);
    return v_res_1670_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Array_instInhabited(lean_box(0));
    return v___x_1671_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(
    mut v_fixedParamPerms_1672_: *mut LeanObject,
    mut v_fixedArgs_1673_: *mut LeanObject,
    mut v_as_1674_: *mut LeanObject,
    mut v_sz_1675_: usize,
    mut v_i_1676_: usize,
    mut v_b_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v_fst_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1697_: u8 = 0;
    let mut v_fst_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v_array_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v_array_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_next_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v_ref_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: usize = 0;
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_reuseFailAlloc_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_a_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut v_unused_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_reuseFailAlloc_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut v_unused_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1829_: u8 = 0;
    let mut v_unused_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut v_unused_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut v_unused_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_unused_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1685_ = lean_usize_dec_lt(v_i_1676_, v_sz_1675_);
                if v___x_1685_ == 0 {
                    lean_dec_ref(v_fixedArgs_1673_);
                    v___x_1686_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1686_, 0, v_b_1677_);
                    return v___x_1686_;
                } else {
                    v_snd_1687_ = lean_ctor_get(v_b_1677_, 1);
                    lean_inc(v_snd_1687_);
                    v_snd_1688_ = lean_ctor_get(v_snd_1687_, 1);
                    lean_inc(v_snd_1688_);
                    v_snd_1689_ = lean_ctor_get(v_snd_1688_, 1);
                    lean_inc(v_snd_1689_);
                    v_fst_1690_ = lean_ctor_get(v_b_1677_, 0);
                    v_isSharedCheck_1837_ = (!lean_is_exclusive(v_b_1677_)) as u8;
                    if v_isSharedCheck_1837_ == 0 {
                        v_unused_1838_ = lean_ctor_get(v_b_1677_, 1);
                        lean_dec(v_unused_1838_);
                        v___x_1692_ = v_b_1677_;
                        v_isShared_1693_ = v_isSharedCheck_1837_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_1690_);
                        lean_dec(v_b_1677_);
                        v___x_1692_ = lean_box(0);
                        v_isShared_1693_ = v_isSharedCheck_1837_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1694_ = lean_ctor_get(v_snd_1687_, 0);
                v_isSharedCheck_1835_ = (!lean_is_exclusive(v_snd_1687_)) as u8;
                if v_isSharedCheck_1835_ == 0 {
                    v_unused_1836_ = lean_ctor_get(v_snd_1687_, 1);
                    lean_dec(v_unused_1836_);
                    v___x_1696_ = v_snd_1687_;
                    v_isShared_1697_ = v_isSharedCheck_1835_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_1694_);
                    lean_dec(v_snd_1687_);
                    v___x_1696_ = lean_box(0);
                    v_isShared_1697_ = v_isSharedCheck_1835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1698_ = lean_ctor_get(v_snd_1688_, 0);
                v_isSharedCheck_1833_ = (!lean_is_exclusive(v_snd_1688_)) as u8;
                if v_isSharedCheck_1833_ == 0 {
                    v_unused_1834_ = lean_ctor_get(v_snd_1688_, 1);
                    lean_dec(v_unused_1834_);
                    v___x_1700_ = v_snd_1688_;
                    v_isShared_1701_ = v_isSharedCheck_1833_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_1698_);
                    lean_dec(v_snd_1688_);
                    v___x_1700_ = lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_array_1702_ = lean_ctor_get(v_snd_1689_, 0);
                v_start_1703_ = lean_ctor_get(v_snd_1689_, 1);
                v_stop_1704_ = lean_ctor_get(v_snd_1689_, 2);
                v___x_1705_ = lean_nat_dec_lt(v_start_1703_, v_stop_1704_);
                if v___x_1705_ == 0 {
                    lean_dec_ref(v_fixedArgs_1673_);
                    if v_isShared_1701_ == 0 {
                        v___x_1707_ = v___x_1700_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_fst_1698_);
                        lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_snd_1689_);
                        v___x_1707_ = v_reuseFailAlloc_1715_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_1704_);
                    lean_inc(v_start_1703_);
                    lean_inc_ref(v_array_1702_);
                    v_isSharedCheck_1829_ = (!lean_is_exclusive(v_snd_1689_)) as u8;
                    if v_isSharedCheck_1829_ == 0 {
                        v_unused_1830_ = lean_ctor_get(v_snd_1689_, 2);
                        lean_dec(v_unused_1830_);
                        v_unused_1831_ = lean_ctor_get(v_snd_1689_, 1);
                        lean_dec(v_unused_1831_);
                        v_unused_1832_ = lean_ctor_get(v_snd_1689_, 0);
                        lean_dec(v_unused_1832_);
                        v___x_1717_ = v_snd_1689_;
                        v_isShared_1718_ = v_isSharedCheck_1829_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v_snd_1689_);
                        v___x_1717_ = lean_box(0);
                        v_isShared_1718_ = v_isSharedCheck_1829_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1697_ == 0 {
                    lean_ctor_set(v___x_1696_, 1, v___x_1707_);
                    v___x_1709_ = v___x_1696_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_fst_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1707_);
                    v___x_1709_ = v_reuseFailAlloc_1714_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1693_ == 0 {
                    lean_ctor_set(v___x_1692_, 1, v___x_1709_);
                    v___x_1711_ = v___x_1692_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_fst_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1713_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1712_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1712_, 0, v___x_1711_);
                return v___x_1712_;
            }
            7 => {
                v_array_1719_ = lean_ctor_get(v_fst_1698_, 0);
                v_start_1720_ = lean_ctor_get(v_fst_1698_, 1);
                v_stop_1721_ = lean_ctor_get(v_fst_1698_, 2);
                v___x_1722_ = lean_array_fget(v_array_1702_, v_start_1703_);
                v___x_1723_ = lean_unsigned_to_nat(1);
                v___x_1724_ = lean_nat_add(v_start_1703_, v___x_1723_);
                lean_dec(v_start_1703_);
                if v_isShared_1718_ == 0 {
                    lean_ctor_set(v___x_1717_, 1, v___x_1724_);
                    v___x_1726_ = v___x_1717_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_array_1702_);
                    lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1724_);
                    lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_stop_1704_);
                    v___x_1726_ = v_reuseFailAlloc_1828_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1727_ = lean_nat_dec_lt(v_start_1720_, v_stop_1721_);
                if v___x_1727_ == 0 {
                    lean_dec(v___x_1722_);
                    lean_dec_ref(v_fixedArgs_1673_);
                    if v_isShared_1701_ == 0 {
                        lean_ctor_set(v___x_1700_, 1, v___x_1726_);
                        v___x_1729_ = v___x_1700_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_fst_1698_);
                        lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1726_);
                        v___x_1729_ = v_reuseFailAlloc_1737_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_1721_);
                    lean_inc(v_start_1720_);
                    lean_inc_ref(v_array_1719_);
                    v_isSharedCheck_1824_ = (!lean_is_exclusive(v_fst_1698_)) as u8;
                    if v_isSharedCheck_1824_ == 0 {
                        v_unused_1825_ = lean_ctor_get(v_fst_1698_, 2);
                        lean_dec(v_unused_1825_);
                        v_unused_1826_ = lean_ctor_get(v_fst_1698_, 1);
                        lean_dec(v_unused_1826_);
                        v_unused_1827_ = lean_ctor_get(v_fst_1698_, 0);
                        lean_dec(v_unused_1827_);
                        v___x_1739_ = v_fst_1698_;
                        v_isShared_1740_ = v_isSharedCheck_1824_;
                        state = 12;
                        continue;
                    } else {
                        lean_dec(v_fst_1698_);
                        v___x_1739_ = lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1824_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1697_ == 0 {
                    lean_ctor_set(v___x_1696_, 1, v___x_1729_);
                    v___x_1731_ = v___x_1696_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_fst_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1729_);
                    v___x_1731_ = v_reuseFailAlloc_1736_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1693_ == 0 {
                    lean_ctor_set(v___x_1692_, 1, v___x_1731_);
                    v___x_1733_ = v___x_1692_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_fst_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1731_);
                    v___x_1733_ = v_reuseFailAlloc_1735_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1734_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1734_, 0, v___x_1733_);
                return v___x_1734_;
            }
            12 => {
                v_next_1741_ = lean_ctor_get(v_fst_1694_, 0);
                lean_inc(v_next_1741_);
                v_upperBound_1742_ = lean_ctor_get(v_fst_1694_, 1);
                v___x_1743_ = lean_array_fget(v_array_1719_, v_start_1720_);
                v___x_1744_ = lean_nat_add(v_start_1720_, v___x_1723_);
                lean_dec(v_start_1720_);
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 1, v___x_1744_);
                    v___x_1746_ = v___x_1739_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_array_1719_);
                    lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1744_);
                    lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_stop_1721_);
                    v___x_1746_ = v_reuseFailAlloc_1823_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if lean_obj_tag(v_next_1741_) == 0 {
                    lean_dec(v___x_1743_);
                    lean_dec(v___x_1722_);
                    lean_dec_ref(v_fixedArgs_1673_);
                    state = 14;
                    continue;
                } else {
                    v_val_1758_ = lean_ctor_get(v_next_1741_, 0);
                    v_isSharedCheck_1822_ = (!lean_is_exclusive(v_next_1741_)) as u8;
                    if v_isSharedCheck_1822_ == 0 {
                        v___x_1760_ = v_next_1741_;
                        v_isShared_1761_ = v_isSharedCheck_1822_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_val_1758_);
                        lean_dec(v_next_1741_);
                        v___x_1760_ = lean_box(0);
                        v_isShared_1761_ = v_isSharedCheck_1822_;
                        state = 18;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1701_ == 0 {
                    lean_ctor_set(v___x_1700_, 1, v___x_1726_);
                    lean_ctor_set(v___x_1700_, 0, v___x_1746_);
                    v___x_1749_ = v___x_1700_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1746_);
                    lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1726_);
                    v___x_1749_ = v_reuseFailAlloc_1757_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1697_ == 0 {
                    lean_ctor_set(v___x_1696_, 1, v___x_1749_);
                    v___x_1751_ = v___x_1696_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_fst_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1749_);
                    v___x_1751_ = v_reuseFailAlloc_1756_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1693_ == 0 {
                    lean_ctor_set(v___x_1692_, 1, v___x_1751_);
                    v___x_1753_ = v___x_1692_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_fst_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1751_);
                    v___x_1753_ = v_reuseFailAlloc_1755_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1754_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                return v___x_1754_;
            }
            18 => {
                v___x_1762_ = lean_nat_dec_lt(v_val_1758_, v_upperBound_1742_);
                if v___x_1762_ == 0 {
                    lean_del_object(v___x_1760_);
                    lean_dec(v_val_1758_);
                    lean_dec(v___x_1743_);
                    lean_dec(v___x_1722_);
                    lean_dec_ref(v_fixedArgs_1673_);
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_upperBound_1742_);
                    lean_del_object(v___x_1700_);
                    lean_del_object(v___x_1696_);
                    lean_del_object(v___x_1692_);
                    v_isSharedCheck_1819_ = (!lean_is_exclusive(v_fst_1694_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v_unused_1820_ = lean_ctor_get(v_fst_1694_, 1);
                        lean_dec(v_unused_1820_);
                        v_unused_1821_ = lean_ctor_get(v_fst_1694_, 0);
                        lean_dec(v_unused_1821_);
                        v___x_1764_ = v_fst_1694_;
                        v_isShared_1765_ = v_isSharedCheck_1819_;
                        state = 19;
                        continue;
                    } else {
                        lean_dec(v_fst_1694_);
                        v___x_1764_ = lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1819_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                v_ref_1766_ = lean_ctor_get(v___x_1722_, 0);
                lean_inc(v_ref_1766_);
                v_fn_1767_ = lean_ctor_get(v___x_1722_, 1);
                lean_inc_ref(v_fn_1767_);
                lean_dec(v___x_1722_);
                lean_inc(v___y_1683_);
                lean_inc_ref(v___y_1682_);
                lean_inc(v___y_1681_);
                lean_inc_ref(v___y_1680_);
                v___x_1768_ = lean_infer_type(
                    v_fn_1767_,
                    v___y_1680_,
                    v___y_1681_,
                    v___y_1682_,
                    v___y_1683_,
                );
                if lean_obj_tag(v___x_1768_) == 0 {
                    v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
                    lean_inc(v_a_1769_);
                    lean_dec_ref_known(v___x_1768_, 1);
                    v_perms_1770_ = lean_ctor_get(v_fixedParamPerms_1672_, 1);
                    v___x_1771_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
                    v___x_1772_ = lean_array_get_borrowed(v___x_1771_, v_perms_1770_, v_val_1758_);
                    lean_inc_ref(v_fixedArgs_1673_);
                    lean_inc(v___x_1772_);
                    v___x_1773_ = l_Lean_Elab_FixedParamPerm_instantiateForall(
                        v___x_1772_,
                        v_a_1769_,
                        v_fixedArgs_1673_,
                        v___y_1680_,
                        v___y_1681_,
                        v___y_1682_,
                        v___y_1683_,
                    );
                    if lean_obj_tag(v___x_1773_) == 0 {
                        v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
                        lean_inc_n(v_a_1774_, 2);
                        lean_dec_ref_known(v___x_1773_, 1);
                        v_a_1775_ = lean_array_uget_borrowed(v_as_1674_, v_i_1676_);
                        lean_inc(v_a_1775_);
                        lean_inc(v___x_1743_);
                        v___f_1776_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___boxed as *mut core::ffi::c_void, 13, 4);
                        lean_closure_set(v___f_1776_, 0, v___x_1743_);
                        lean_closure_set(v___f_1776_, 1, v_a_1775_);
                        lean_closure_set(v___f_1776_, 2, v_a_1774_);
                        lean_closure_set(v___f_1776_, 3, v_ref_1766_);
                        if v_isShared_1761_ == 0 {
                            lean_ctor_set(v___x_1760_, 0, v___x_1743_);
                            v___x_1778_ = v___x_1760_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1743_);
                            v___x_1778_ = v_reuseFailAlloc_1802_;
                            state = 20;
                            continue;
                        }
                    } else {
                        lean_dec(v_ref_1766_);
                        lean_del_object(v___x_1764_);
                        lean_del_object(v___x_1760_);
                        lean_dec(v_val_1758_);
                        lean_dec_ref(v___x_1746_);
                        lean_dec(v___x_1743_);
                        lean_dec(v_upperBound_1742_);
                        lean_dec_ref(v___x_1726_);
                        lean_dec(v_fst_1690_);
                        lean_dec_ref(v_fixedArgs_1673_);
                        v_a_1803_ = lean_ctor_get(v___x_1773_, 0);
                        v_isSharedCheck_1810_ = (!lean_is_exclusive(v___x_1773_)) as u8;
                        if v_isSharedCheck_1810_ == 0 {
                            v___x_1805_ = v___x_1773_;
                            v_isShared_1806_ = v_isSharedCheck_1810_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_1803_);
                            lean_dec(v___x_1773_);
                            v___x_1805_ = lean_box(0);
                            v_isShared_1806_ = v_isSharedCheck_1810_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_ref_1766_);
                    lean_del_object(v___x_1764_);
                    lean_del_object(v___x_1760_);
                    lean_dec(v_val_1758_);
                    lean_dec_ref(v___x_1746_);
                    lean_dec(v___x_1743_);
                    lean_dec(v_upperBound_1742_);
                    lean_dec_ref(v___x_1726_);
                    lean_dec(v_fst_1690_);
                    lean_dec_ref(v_fixedArgs_1673_);
                    v_a_1811_ = lean_ctor_get(v___x_1768_, 0);
                    v_isSharedCheck_1818_ = (!lean_is_exclusive(v___x_1768_)) as u8;
                    if v_isSharedCheck_1818_ == 0 {
                        v___x_1813_ = v___x_1768_;
                        v_isShared_1814_ = v_isSharedCheck_1818_;
                        state = 26;
                        continue;
                    } else {
                        lean_inc(v_a_1811_);
                        lean_dec(v___x_1768_);
                        v___x_1813_ = lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1818_;
                        state = 26;
                        continue;
                    }
                }
            }
            20 => {
                v___x_1779_ = 0;
                v___x_1780_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_checkCodomains_spec__5___redArg(v_a_1774_, v___x_1778_, v___f_1776_, v___x_1779_, v___x_1779_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
                if lean_obj_tag(v___x_1780_) == 0 {
                    v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
                    lean_inc(v_a_1781_);
                    lean_dec_ref_known(v___x_1780_, 1);
                    v___x_1782_ = lean_nat_add(v_val_1758_, v___x_1723_);
                    lean_dec(v_val_1758_);
                    v___x_1783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1783_, 0, v___x_1782_);
                    if v_isShared_1765_ == 0 {
                        lean_ctor_set(v___x_1764_, 0, v___x_1783_);
                        v___x_1785_ = v___x_1764_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1783_);
                        lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_upperBound_1742_);
                        v___x_1785_ = v_reuseFailAlloc_1793_;
                        state = 21;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1764_);
                    lean_dec(v_val_1758_);
                    lean_dec_ref(v___x_1746_);
                    lean_dec(v_upperBound_1742_);
                    lean_dec_ref(v___x_1726_);
                    lean_dec(v_fst_1690_);
                    lean_dec_ref(v_fixedArgs_1673_);
                    v_a_1794_ = lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1780_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_1794_);
                        lean_dec(v___x_1780_);
                        v___x_1796_ = lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 22;
                        continue;
                    }
                }
            }
            21 => {
                v___x_1786_ = lean_array_push(v_fst_1690_, v_a_1781_);
                v___x_1787_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1787_, 0, v___x_1746_);
                lean_ctor_set(v___x_1787_, 1, v___x_1726_);
                v___x_1788_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1788_, 0, v___x_1785_);
                lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1789_, 0, v___x_1786_);
                lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = 1usize;
                v___x_1791_ = lean_usize_add(v_i_1676_, v___x_1790_);
                v_i_1676_ = v___x_1791_;
                v_b_1677_ = v___x_1789_;
                state = 0;
                continue;
            }
            22 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1799_;
            }
            24 => {
                if v_isShared_1806_ == 0 {
                    v___x_1808_ = v___x_1805_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
                    v___x_1808_ = v_reuseFailAlloc_1809_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1808_;
            }
            26 => {
                if v_isShared_1814_ == 0 {
                    v___x_1816_ = v___x_1813_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
                    v___x_1816_ = v_reuseFailAlloc_1817_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___boxed(
    mut v_fixedParamPerms_1839_: *mut LeanObject,
    mut v_fixedArgs_1840_: *mut LeanObject,
    mut v_as_1841_: *mut LeanObject,
    mut v_sz_1842_: *mut LeanObject,
    mut v_i_1843_: *mut LeanObject,
    mut v_b_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1852_: usize = 0;
    let mut v_i_boxed_1853_: usize = 0;
    let mut v_res_1854_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1852_ = lean_unbox_usize(v_sz_1842_);
    lean_dec(v_sz_1842_);
    v_i_boxed_1853_ = lean_unbox_usize(v_i_1843_);
    lean_dec(v_i_1843_);
    v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_1839_, v_fixedArgs_1840_, v_as_1841_, v_sz_boxed_1852_, v_i_boxed_1853_, v_b_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
    lean_dec(v___y_1850_);
    lean_dec_ref(v___y_1849_);
    lean_dec(v___y_1848_);
    lean_dec_ref(v___y_1847_);
    lean_dec(v___y_1846_);
    lean_dec_ref(v___y_1845_);
    lean_dec_ref(v_as_1841_);
    lean_dec_ref(v_fixedParamPerms_1839_);
    return v_res_1854_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    v___x_1856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__0;
    v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
    return v___x_1857_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__2;
    v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__4;
    v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__6;
    v___x_1866_ = l_Lean_stringToMessageData(v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(
    mut v_upperBound_1867_: *mut LeanObject,
    mut v___x_1868_: *mut LeanObject,
    mut v___x_1869_: *mut LeanObject,
    mut v_termMeasures_1870_: *mut LeanObject,
    mut v_names_1871_: *mut LeanObject,
    mut v_a_1872_: *mut LeanObject,
    mut v_b_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1886_ = lean_nat_dec_lt(v_a_1872_, v_upperBound_1867_);
                if v___x_1886_ == 0 {
                    lean_dec(v_a_1872_);
                    lean_dec_ref(v___x_1869_);
                    v___x_1887_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1887_, 0, v_b_1873_);
                    return v___x_1887_;
                } else {
                    v___x_1888_ = lean_array_fget_borrowed(v___x_1868_, v_a_1872_);
                    lean_inc(v___x_1888_);
                    lean_inc_ref(v___x_1869_);
                    v___x_1889_ = l_Lean_Meta_isExprDefEqGuarded(
                        v___x_1869_,
                        v___x_1888_,
                        v___y_1876_,
                        v___y_1877_,
                        v___y_1878_,
                        v___y_1879_,
                    );
                    if lean_obj_tag(v___x_1889_) == 0 {
                        v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
                        lean_inc(v_a_1890_);
                        lean_dec_ref_known(v___x_1889_, 1);
                        v___x_1891_ = lean_box(0);
                        v___x_1892_ = (lean_unbox(v_a_1890_) as u8);
                        lean_dec(v_a_1890_);
                        if v___x_1892_ == 0 {
                            v___x_1893_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
                            v___x_1894_ = lean_array_get_borrowed(
                                v___x_1893_,
                                v_termMeasures_1870_,
                                v_a_1872_,
                            );
                            v_ref_1895_ = lean_ctor_get(v___x_1894_, 0);
                            v___x_1896_ = lean_unsigned_to_nat(0);
                            v___x_1897_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__1);
                            v___x_1898_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__3);
                            v___x_1899_ = lean_box(0);
                            v___x_1900_ =
                                lean_array_get_borrowed(v___x_1899_, v_names_1871_, v___x_1896_);
                            lean_inc(v___x_1900_);
                            v___x_1901_ = l_Lean_MessageData_ofName(v___x_1900_);
                            v___x_1902_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1902_, 0, v___x_1898_);
                            lean_ctor_set(v___x_1902_, 1, v___x_1901_);
                            v___x_1903_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__5);
                            v___x_1904_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1904_, 0, v___x_1902_);
                            lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                            v___x_1905_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1905_, 0, v___x_1897_);
                            lean_ctor_set(v___x_1905_, 1, v___x_1904_);
                            lean_inc_ref(v___x_1869_);
                            v___x_1906_ = l_Lean_indentExpr(v___x_1869_);
                            v___x_1907_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__11);
                            v___x_1908_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1908_, 0, v___x_1906_);
                            lean_ctor_set(v___x_1908_, 1, v___x_1907_);
                            v___x_1909_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1909_, 0, v___x_1905_);
                            lean_ctor_set(v___x_1909_, 1, v___x_1908_);
                            v___x_1910_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___closed__7);
                            v___x_1911_ =
                                lean_array_get_borrowed(v___x_1899_, v_names_1871_, v_a_1872_);
                            lean_inc(v___x_1911_);
                            v___x_1912_ = l_Lean_MessageData_ofName(v___x_1911_);
                            v___x_1913_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1913_, 0, v___x_1910_);
                            lean_ctor_set(v___x_1913_, 1, v___x_1912_);
                            v___x_1914_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1914_, 0, v___x_1913_);
                            lean_ctor_set(v___x_1914_, 1, v___x_1903_);
                            lean_inc(v___x_1888_);
                            v___x_1915_ = l_Lean_indentExpr(v___x_1888_);
                            v___x_1916_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1916_, 0, v___x_1914_);
                            lean_ctor_set(v___x_1916_, 1, v___x_1915_);
                            v___x_1917_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1917_, 0, v___x_1916_);
                            lean_ctor_set(v___x_1917_, 1, v___x_1907_);
                            v___x_1918_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1918_, 0, v___x_1909_);
                            lean_ctor_set(v___x_1918_, 1, v___x_1917_);
                            v___x_1919_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___lam__0___closed__14);
                            v___x_1920_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1920_, 0, v___x_1918_);
                            lean_ctor_set(v___x_1920_, 1, v___x_1919_);
                            v___x_1921_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(v_ref_1895_, v___x_1920_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
                            if lean_obj_tag(v___x_1921_) == 0 {
                                lean_dec_ref_known(v___x_1921_, 1);
                                v_a_1882_ = v___x_1891_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_1872_);
                                lean_dec_ref(v___x_1869_);
                                return v___x_1921_;
                            }
                        } else {
                            v_a_1882_ = v___x_1891_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1872_);
                        lean_dec_ref(v___x_1869_);
                        v_a_1922_ = lean_ctor_get(v___x_1889_, 0);
                        v_isSharedCheck_1929_ = (!lean_is_exclusive(v___x_1889_)) as u8;
                        if v_isSharedCheck_1929_ == 0 {
                            v___x_1924_ = v___x_1889_;
                            v_isShared_1925_ = v_isSharedCheck_1929_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1922_);
                            lean_dec(v___x_1889_);
                            v___x_1924_ = lean_box(0);
                            v_isShared_1925_ = v_isSharedCheck_1929_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1883_ = lean_unsigned_to_nat(1);
                v___x_1884_ = lean_nat_add(v_a_1872_, v___x_1883_);
                lean_dec(v_a_1872_);
                v_a_1872_ = v___x_1884_;
                v_b_1873_ = v_a_1882_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1925_ == 0 {
                    v___x_1927_ = v___x_1924_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
                    v___x_1927_ = v_reuseFailAlloc_1928_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg___boxed(
    mut v_upperBound_1930_: *mut LeanObject,
    mut v___x_1931_: *mut LeanObject,
    mut v___x_1932_: *mut LeanObject,
    mut v_termMeasures_1933_: *mut LeanObject,
    mut v_names_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_b_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1944_: *mut LeanObject = core::ptr::null_mut();
    v_res_1944_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(
            v_upperBound_1930_,
            v___x_1931_,
            v___x_1932_,
            v_termMeasures_1933_,
            v_names_1934_,
            v_a_1935_,
            v_b_1936_,
            v___y_1937_,
            v___y_1938_,
            v___y_1939_,
            v___y_1940_,
            v___y_1941_,
            v___y_1942_,
        );
    lean_dec(v___y_1942_);
    lean_dec_ref(v___y_1941_);
    lean_dec(v___y_1940_);
    lean_dec_ref(v___y_1939_);
    lean_dec(v___y_1938_);
    lean_dec_ref(v___y_1937_);
    lean_dec_ref(v_names_1934_);
    lean_dec_ref(v_termMeasures_1933_);
    lean_dec_ref(v___x_1931_);
    lean_dec(v_upperBound_1930_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_Elab_WF_checkCodomains(
    mut v_names_1949_: *mut LeanObject,
    mut v_fixedParamPerms_1950_: *mut LeanObject,
    mut v_fixedArgs_1951_: *mut LeanObject,
    mut v_arities_1952_: *mut LeanObject,
    mut v_termMeasures_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_codomains_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1973_: usize = 0;
    let mut v___x_1974_: usize = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v_unused_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1961_ = lean_unsigned_to_nat(0);
                v_codomains_1962_ = l_Lean_Elab_WF_checkCodomains___closed__0;
                v___x_1963_ = lean_array_get_size(v_names_1949_);
                v___x_1964_ = l_Lean_Elab_WF_checkCodomains___closed__1;
                v___x_1965_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1965_, 0, v___x_1964_);
                lean_ctor_set(v___x_1965_, 1, v___x_1963_);
                v___x_1966_ = lean_array_get_size(v_arities_1952_);
                v___x_1967_ =
                    l_Array_toSubarray___redArg(v_arities_1952_, v___x_1961_, v___x_1966_);
                v___x_1968_ = lean_array_get_size(v_termMeasures_1953_);
                lean_inc_ref(v_termMeasures_1953_);
                v___x_1969_ =
                    l_Array_toSubarray___redArg(v_termMeasures_1953_, v___x_1961_, v___x_1968_);
                v___x_1970_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1970_, 0, v___x_1967_);
                lean_ctor_set(v___x_1970_, 1, v___x_1969_);
                v___x_1971_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1971_, 0, v___x_1965_);
                lean_ctor_set(v___x_1971_, 1, v___x_1970_);
                v___x_1972_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1972_, 0, v_codomains_1962_);
                lean_ctor_set(v___x_1972_, 1, v___x_1971_);
                v_sz_1973_ = lean_array_size(v_names_1949_);
                v___x_1974_ = 0usize;
                v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6(v_fixedParamPerms_1950_, v_fixedArgs_1951_, v_names_1949_, v_sz_1973_, v___x_1974_, v___x_1972_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
                if lean_obj_tag(v___x_1975_) == 0 {
                    v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
                    lean_inc(v_a_1976_);
                    lean_dec_ref_known(v___x_1975_, 1);
                    v_fst_1977_ = lean_ctor_get(v_a_1976_, 0);
                    lean_inc(v_fst_1977_);
                    lean_dec(v_a_1976_);
                    v___x_1978_ = l_Lean_instInhabitedExpr;
                    v___x_1979_ = lean_unsigned_to_nat(1);
                    v___x_1980_ = lean_array_get_size(v_fst_1977_);
                    v___x_1981_ = lean_array_get(v___x_1978_, v_fst_1977_, v___x_1961_);
                    v___x_1982_ = lean_box(0);
                    lean_inc(v___x_1981_);
                    v___x_1983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(v___x_1980_, v_fst_1977_, v___x_1981_, v_termMeasures_1953_, v_names_1949_, v___x_1979_, v___x_1982_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
                    lean_dec_ref(v_termMeasures_1953_);
                    lean_dec(v_fst_1977_);
                    if lean_obj_tag(v___x_1983_) == 0 {
                        v_isSharedCheck_1990_ = (!lean_is_exclusive(v___x_1983_)) as u8;
                        if v_isSharedCheck_1990_ == 0 {
                            v_unused_1991_ = lean_ctor_get(v___x_1983_, 0);
                            lean_dec(v_unused_1991_);
                            v___x_1985_ = v___x_1983_;
                            v_isShared_1986_ = v_isSharedCheck_1990_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1983_);
                            v___x_1985_ = lean_box(0);
                            v_isShared_1986_ = v_isSharedCheck_1990_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1981_);
                        v_a_1992_ = lean_ctor_get(v___x_1983_, 0);
                        v_isSharedCheck_1999_ = (!lean_is_exclusive(v___x_1983_)) as u8;
                        if v_isSharedCheck_1999_ == 0 {
                            v___x_1994_ = v___x_1983_;
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1992_);
                            lean_dec(v___x_1983_);
                            v___x_1994_ = lean_box(0);
                            v_isShared_1995_ = v_isSharedCheck_1999_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_termMeasures_1953_);
                    v_a_2000_ = lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2007_ = (!lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2007_ == 0 {
                        v___x_2002_ = v___x_1975_;
                        v_isShared_2003_ = v_isSharedCheck_2007_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2000_);
                        lean_dec(v___x_1975_);
                        v___x_2002_ = lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2007_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1986_ == 0 {
                    lean_ctor_set(v___x_1985_, 0, v___x_1981_);
                    v___x_1988_ = v___x_1985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1981_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1988_;
            }
            3 => {
                if v_isShared_1995_ == 0 {
                    v___x_1997_ = v___x_1994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_1998_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1997_;
            }
            5 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_checkCodomains___boxed(
    mut v_names_2008_: *mut LeanObject,
    mut v_fixedParamPerms_2009_: *mut LeanObject,
    mut v_fixedArgs_2010_: *mut LeanObject,
    mut v_arities_2011_: *mut LeanObject,
    mut v_termMeasures_2012_: *mut LeanObject,
    mut v_a_2013_: *mut LeanObject,
    mut v_a_2014_: *mut LeanObject,
    mut v_a_2015_: *mut LeanObject,
    mut v_a_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Lean_Elab_WF_checkCodomains(
        v_names_2008_,
        v_fixedParamPerms_2009_,
        v_fixedArgs_2010_,
        v_arities_2011_,
        v_termMeasures_2012_,
        v_a_2013_,
        v_a_2014_,
        v_a_2015_,
        v_a_2016_,
        v_a_2017_,
        v_a_2018_,
    );
    lean_dec(v_a_2018_);
    lean_dec_ref(v_a_2017_);
    lean_dec(v_a_2016_);
    lean_dec_ref(v_a_2015_);
    lean_dec(v_a_2014_);
    lean_dec_ref(v_a_2013_);
    lean_dec_ref(v_fixedParamPerms_2009_);
    lean_dec_ref(v_names_2008_);
    return v_res_2020_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(
    mut v_00_u03b1_2021_: *mut LeanObject,
    mut v_ref_2022_: *mut LeanObject,
    mut v_msg_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___redArg(
        v_ref_2022_,
        v_msg_2023_,
        v___y_2024_,
        v___y_2025_,
        v___y_2026_,
        v___y_2027_,
        v___y_2028_,
        v___y_2029_,
    );
    return v___x_2031_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4___boxed(
    mut v_00_u03b1_2032_: *mut LeanObject,
    mut v_ref_2033_: *mut LeanObject,
    mut v_msg_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2042_: *mut LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4(
        v_00_u03b1_2032_,
        v_ref_2033_,
        v_msg_2034_,
        v___y_2035_,
        v___y_2036_,
        v___y_2037_,
        v___y_2038_,
        v___y_2039_,
        v___y_2040_,
    );
    lean_dec(v___y_2040_);
    lean_dec_ref(v___y_2039_);
    lean_dec(v___y_2038_);
    lean_dec_ref(v___y_2037_);
    lean_dec(v___y_2036_);
    lean_dec_ref(v___y_2035_);
    lean_dec(v_ref_2033_);
    return v_res_2042_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(
    mut v_upperBound_2043_: *mut LeanObject,
    mut v___x_2044_: *mut LeanObject,
    mut v___x_2045_: *mut LeanObject,
    mut v_termMeasures_2046_: *mut LeanObject,
    mut v_names_2047_: *mut LeanObject,
    mut v_inst_2048_: *mut LeanObject,
    mut v_R_2049_: *mut LeanObject,
    mut v_a_2050_: *mut LeanObject,
    mut v_b_2051_: *mut LeanObject,
    mut v_c_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    v___x_2060_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___redArg(
            v_upperBound_2043_,
            v___x_2044_,
            v___x_2045_,
            v_termMeasures_2046_,
            v_names_2047_,
            v_a_2050_,
            v_b_2051_,
            v___y_2053_,
            v___y_2054_,
            v___y_2055_,
            v___y_2056_,
            v___y_2057_,
            v___y_2058_,
        );
    return v___x_2060_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_2061_: *mut LeanObject = *_args.add(0);
    let mut v___x_2062_: *mut LeanObject = *_args.add(1);
    let mut v___x_2063_: *mut LeanObject = *_args.add(2);
    let mut v_termMeasures_2064_: *mut LeanObject = *_args.add(3);
    let mut v_names_2065_: *mut LeanObject = *_args.add(4);
    let mut v_inst_2066_: *mut LeanObject = *_args.add(5);
    let mut v_R_2067_: *mut LeanObject = *_args.add(6);
    let mut v_a_2068_: *mut LeanObject = *_args.add(7);
    let mut v_b_2069_: *mut LeanObject = *_args.add(8);
    let mut v_c_2070_: *mut LeanObject = *_args.add(9);
    let mut v___y_2071_: *mut LeanObject = *_args.add(10);
    let mut v___y_2072_: *mut LeanObject = *_args.add(11);
    let mut v___y_2073_: *mut LeanObject = *_args.add(12);
    let mut v___y_2074_: *mut LeanObject = *_args.add(13);
    let mut v___y_2075_: *mut LeanObject = *_args.add(14);
    let mut v___y_2076_: *mut LeanObject = *_args.add(15);
    let mut v___y_2077_: *mut LeanObject = *_args.add(16);
    let mut v_res_2078_: *mut LeanObject = core::ptr::null_mut();
    v_res_2078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_WF_checkCodomains_spec__7(
        v_upperBound_2061_,
        v___x_2062_,
        v___x_2063_,
        v_termMeasures_2064_,
        v_names_2065_,
        v_inst_2066_,
        v_R_2067_,
        v_a_2068_,
        v_b_2069_,
        v_c_2070_,
        v___y_2071_,
        v___y_2072_,
        v___y_2073_,
        v___y_2074_,
        v___y_2075_,
        v___y_2076_,
    );
    lean_dec(v___y_2076_);
    lean_dec_ref(v___y_2075_);
    lean_dec(v___y_2074_);
    lean_dec_ref(v___y_2073_);
    lean_dec(v___y_2072_);
    lean_dec_ref(v___y_2071_);
    lean_dec_ref(v_names_2065_);
    lean_dec_ref(v_termMeasures_2064_);
    lean_dec_ref(v___x_2062_);
    lean_dec(v_upperBound_2061_);
    return v_res_2078_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(
    mut v_00_u03b1_2079_: *mut LeanObject,
    mut v_msg_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    v___x_2088_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___redArg(v_msg_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
    return v___x_2088_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5___boxed(
    mut v_00_u03b1_2089_: *mut LeanObject,
    mut v_msg_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2098_: *mut LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5(v_00_u03b1_2089_, v_msg_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
    lean_dec(v___y_2096_);
    lean_dec_ref(v___y_2095_);
    lean_dec(v___y_2094_);
    lean_dec_ref(v___y_2093_);
    lean_dec(v___y_2092_);
    lean_dec_ref(v___y_2091_);
    return v_res_2098_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(
    mut v_msgData_2099_: *mut LeanObject,
    mut v_macroStack_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    v___x_2108_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___redArg(v_msgData_2099_, v_macroStack_2100_, v___y_2105_);
    return v___x_2108_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8___boxed(
    mut v_msgData_2109_: *mut LeanObject,
    mut v_macroStack_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2118_: *mut LeanObject = core::ptr::null_mut();
    v_res_2118_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_WF_checkCodomains_spec__4_spec__5_spec__8(v_msgData_2109_, v_macroStack_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
    lean_dec(v___y_2116_);
    lean_dec_ref(v___y_2115_);
    lean_dec(v___y_2114_);
    lean_dec_ref(v___y_2113_);
    lean_dec(v___y_2112_);
    lean_dec_ref(v___y_2111_);
    return v_res_2118_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(
    mut v_e_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2136_: u8 = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_unused_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2122_ = l_Lean_Expr_hasMVar(v_e_2119_);
                if v___x_2122_ == 0 {
                    v___x_2123_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2123_, 0, v_e_2119_);
                    return v___x_2123_;
                } else {
                    v___x_2124_ = lean_st_ref_get(v___y_2120_);
                    v_mctx_2125_ = lean_ctor_get(v___x_2124_, 0);
                    lean_inc_ref(v_mctx_2125_);
                    lean_dec(v___x_2124_);
                    v___x_2126_ = l_Lean_instantiateMVarsCore(v_mctx_2125_, v_e_2119_);
                    v_fst_2127_ = lean_ctor_get(v___x_2126_, 0);
                    lean_inc(v_fst_2127_);
                    v_snd_2128_ = lean_ctor_get(v___x_2126_, 1);
                    lean_inc(v_snd_2128_);
                    lean_dec_ref(v___x_2126_);
                    v___x_2129_ = lean_st_ref_take(v___y_2120_);
                    v_cache_2130_ = lean_ctor_get(v___x_2129_, 1);
                    v_zetaDeltaFVarIds_2131_ = lean_ctor_get(v___x_2129_, 2);
                    v_postponed_2132_ = lean_ctor_get(v___x_2129_, 3);
                    v_diag_2133_ = lean_ctor_get(v___x_2129_, 4);
                    v_isSharedCheck_2142_ = (!lean_is_exclusive(v___x_2129_)) as u8;
                    if v_isSharedCheck_2142_ == 0 {
                        v_unused_2143_ = lean_ctor_get(v___x_2129_, 0);
                        lean_dec(v_unused_2143_);
                        v___x_2135_ = v___x_2129_;
                        v_isShared_2136_ = v_isSharedCheck_2142_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2133_);
                        lean_inc(v_postponed_2132_);
                        lean_inc(v_zetaDeltaFVarIds_2131_);
                        lean_inc(v_cache_2130_);
                        lean_dec(v___x_2129_);
                        v___x_2135_ = lean_box(0);
                        v_isShared_2136_ = v_isSharedCheck_2142_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2136_ == 0 {
                    lean_ctor_set(v___x_2135_, 0, v_snd_2128_);
                    v___x_2138_ = v___x_2135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_snd_2128_);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_cache_2130_);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_zetaDeltaFVarIds_2131_);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_postponed_2132_);
                    lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_diag_2133_);
                    v___x_2138_ = v_reuseFailAlloc_2141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2139_ = lean_st_ref_set(v___y_2120_, v___x_2138_);
                v___x_2140_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2140_, 0, v_fst_2127_);
                return v___x_2140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg___boxed(
    mut v_e_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2147_: *mut LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(
        v_e_2144_,
        v___y_2145_,
    );
    lean_dec(v___y_2145_);
    return v_res_2147_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(
    mut v_e_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    v___x_2156_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(
        v_e_2148_,
        v___y_2152_,
    );
    return v___x_2156_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___boxed(
    mut v_e_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
    mut v___y_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2165_: *mut LeanObject = core::ptr::null_mut();
    v_res_2165_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1(
        v_e_2157_,
        v___y_2158_,
        v___y_2159_,
        v___y_2160_,
        v___y_2161_,
        v___y_2162_,
        v___y_2163_,
    );
    lean_dec(v___y_2163_);
    lean_dec_ref(v___y_2162_);
    lean_dec(v___y_2161_);
    lean_dec_ref(v___y_2160_);
    lean_dec(v___y_2159_);
    lean_dec_ref(v___y_2158_);
    return v_res_2165_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(
    mut v_fixedParamPerms_2166_: *mut LeanObject,
    mut v_fixedArgs_2167_: *mut LeanObject,
    mut v_as_2168_: *mut LeanObject,
    mut v_i_2169_: *mut LeanObject,
    mut v_j_2170_: *mut LeanObject,
    mut v_bs_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
    mut v___y_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2178_: u8 = 0;
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_perms_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2177_ = lean_unsigned_to_nat(0);
                v_isZero_2178_ = lean_nat_dec_eq(v_i_2169_, v_zero_2177_);
                if v_isZero_2178_ == 1 {
                    lean_dec(v_j_2170_);
                    lean_dec(v_i_2169_);
                    lean_dec_ref(v_fixedArgs_2167_);
                    v___x_2179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2179_, 0, v_bs_2171_);
                    return v___x_2179_;
                } else {
                    v_perms_2180_ = lean_ctor_get(v_fixedParamPerms_2166_, 1);
                    v___x_2181_ = lean_array_fget_borrowed(v_as_2168_, v_j_2170_);
                    v_fn_2182_ = lean_ctor_get(v___x_2181_, 1);
                    v___x_2183_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_checkCodomains_spec__6___closed__0);
                    v___x_2184_ = lean_array_get_borrowed(v___x_2183_, v_perms_2180_, v_j_2170_);
                    lean_inc_ref(v_fixedArgs_2167_);
                    lean_inc_ref(v_fn_2182_);
                    lean_inc(v___x_2184_);
                    v___x_2185_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(
                        v___x_2184_,
                        v_fn_2182_,
                        v_fixedArgs_2167_,
                        v___y_2172_,
                        v___y_2173_,
                        v___y_2174_,
                        v___y_2175_,
                    );
                    if lean_obj_tag(v___x_2185_) == 0 {
                        v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
                        lean_inc(v_a_2186_);
                        lean_dec_ref_known(v___x_2185_, 1);
                        v_one_2187_ = lean_unsigned_to_nat(1);
                        v_n_2188_ = lean_nat_sub(v_i_2169_, v_one_2187_);
                        lean_dec(v_i_2169_);
                        v___x_2189_ = lean_nat_add(v_j_2170_, v_one_2187_);
                        lean_dec(v_j_2170_);
                        v___x_2190_ = lean_array_push(v_bs_2171_, v_a_2186_);
                        v_i_2169_ = v_n_2188_;
                        v_j_2170_ = v___x_2189_;
                        v_bs_2171_ = v___x_2190_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2171_);
                        lean_dec(v_j_2170_);
                        lean_dec(v_i_2169_);
                        lean_dec_ref(v_fixedArgs_2167_);
                        v_a_2192_ = lean_ctor_get(v___x_2185_, 0);
                        v_isSharedCheck_2199_ = (!lean_is_exclusive(v___x_2185_)) as u8;
                        if v_isSharedCheck_2199_ == 0 {
                            v___x_2194_ = v___x_2185_;
                            v_isShared_2195_ = v_isSharedCheck_2199_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2192_);
                            lean_dec(v___x_2185_);
                            v___x_2194_ = lean_box(0);
                            v_isShared_2195_ = v_isSharedCheck_2199_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2195_ == 0 {
                    v___x_2197_ = v___x_2194_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
                    v___x_2197_ = v_reuseFailAlloc_2198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg___boxed(
    mut v_fixedParamPerms_2200_: *mut LeanObject,
    mut v_fixedArgs_2201_: *mut LeanObject,
    mut v_as_2202_: *mut LeanObject,
    mut v_i_2203_: *mut LeanObject,
    mut v_j_2204_: *mut LeanObject,
    mut v_bs_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2211_: *mut LeanObject = core::ptr::null_mut();
    v_res_2211_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(
        v_fixedParamPerms_2200_,
        v_fixedArgs_2201_,
        v_as_2202_,
        v_i_2203_,
        v_j_2204_,
        v_bs_2205_,
        v___y_2206_,
        v___y_2207_,
        v___y_2208_,
        v___y_2209_,
    );
    lean_dec(v___y_2209_);
    lean_dec_ref(v___y_2208_);
    lean_dec(v___y_2207_);
    lean_dec_ref(v___y_2206_);
    lean_dec_ref(v_as_2202_);
    lean_dec_ref(v_fixedParamPerms_2200_);
    return v_res_2211_;
}
pub unsafe fn l_Lean_Elab_WF_elabWFRel___redArg___lam__0(
    mut v_argType_2218_: *mut LeanObject,
    mut v_argsPacker_2219_: *mut LeanObject,
    mut v_declNames_2220_: *mut LeanObject,
    mut v_fixedParamPerms_2221_: *mut LeanObject,
    mut v_fixedArgs_2222_: *mut LeanObject,
    mut v_termMeasures_2223_: *mut LeanObject,
    mut v_k_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut v_a_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v_a_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v_a_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2288_: u8 = 0;
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2292_: u8 = 0;
    let mut v_a_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2300_: u8 = 0;
    let mut v_a_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2304_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_argType_2218_);
                v___x_2232_ = l_Lean_Meta_getLevel(
                    v_argType_2218_,
                    v___y_2227_,
                    v___y_2228_,
                    v___y_2229_,
                    v___y_2230_,
                );
                if lean_obj_tag(v___x_2232_) == 0 {
                    v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
                    lean_inc(v_a_2233_);
                    lean_dec_ref_known(v___x_2232_, 1);
                    lean_inc_ref(v_argsPacker_2219_);
                    v___x_2234_ = l_Lean_Meta_ArgsPacker_arities(v_argsPacker_2219_);
                    lean_inc_ref(v_termMeasures_2223_);
                    lean_inc_ref(v_fixedArgs_2222_);
                    v___x_2235_ = l_Lean_Elab_WF_checkCodomains(
                        v_declNames_2220_,
                        v_fixedParamPerms_2221_,
                        v_fixedArgs_2222_,
                        v___x_2234_,
                        v_termMeasures_2223_,
                        v___y_2225_,
                        v___y_2226_,
                        v___y_2227_,
                        v___y_2228_,
                        v___y_2229_,
                        v___y_2230_,
                    );
                    if lean_obj_tag(v___x_2235_) == 0 {
                        v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
                        lean_inc_n(v_a_2236_, 2);
                        lean_dec_ref_known(v___x_2235_, 1);
                        v___x_2237_ = l_Lean_Meta_getLevel(
                            v_a_2236_,
                            v___y_2227_,
                            v___y_2228_,
                            v___y_2229_,
                            v___y_2230_,
                        );
                        if lean_obj_tag(v___x_2237_) == 0 {
                            v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
                            lean_inc(v_a_2238_);
                            lean_dec_ref_known(v___x_2237_, 1);
                            v___x_2239_ = lean_array_get_size(v_termMeasures_2223_);
                            v___x_2240_ = lean_unsigned_to_nat(0);
                            v___x_2241_ = lean_mk_empty_array_with_capacity(v___x_2239_);
                            v___x_2242_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(v_fixedParamPerms_2221_, v_fixedArgs_2222_, v_termMeasures_2223_, v___x_2239_, v___x_2240_, v___x_2241_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
                            lean_dec_ref(v_termMeasures_2223_);
                            if lean_obj_tag(v___x_2242_) == 0 {
                                v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
                                lean_inc(v_a_2243_);
                                lean_dec_ref_known(v___x_2242_, 1);
                                v___x_2244_ = l_Lean_Meta_ArgsPacker_uncurryND(
                                    v_argsPacker_2219_,
                                    v_a_2243_,
                                    v___y_2227_,
                                    v___y_2228_,
                                    v___y_2229_,
                                    v___y_2230_,
                                );
                                lean_dec(v_a_2243_);
                                lean_dec_ref(v_argsPacker_2219_);
                                if lean_obj_tag(v___x_2244_) == 0 {
                                    v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
                                    lean_inc(v_a_2245_);
                                    lean_dec_ref_known(v___x_2244_, 1);
                                    v___x_2246_ =
                                        l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__1;
                                    v___x_2247_ = lean_box(0);
                                    v___x_2248_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_2248_, 0, v_a_2238_);
                                    lean_ctor_set(v___x_2248_, 1, v___x_2247_);
                                    lean_inc_ref(v___x_2248_);
                                    v___x_2249_ =
                                        l_Lean_Expr_const___override(v___x_2246_, v___x_2248_);
                                    lean_inc(v_a_2236_);
                                    v___x_2250_ =
                                        l_Lean_Expr_app___override(v___x_2249_, v_a_2236_);
                                    v___x_2251_ = lean_box(0);
                                    v___x_2252_ = l_Lean_Meta_synthInstance(
                                        v___x_2250_,
                                        v___x_2251_,
                                        v___y_2227_,
                                        v___y_2228_,
                                        v___y_2229_,
                                        v___y_2230_,
                                    );
                                    if lean_obj_tag(v___x_2252_) == 0 {
                                        v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
                                        lean_inc(v_a_2253_);
                                        lean_dec_ref_known(v___x_2252_, 1);
                                        v___x_2254_ =
                                            l_Lean_Elab_WF_elabWFRel___redArg___lam__0___closed__3;
                                        v___x_2255_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_2255_, 0, v_a_2233_);
                                        lean_ctor_set(v___x_2255_, 1, v___x_2248_);
                                        v___x_2256_ =
                                            l_Lean_Expr_const___override(v___x_2254_, v___x_2255_);
                                        v___x_2257_ = l_Lean_mkApp4(
                                            v___x_2256_,
                                            v_argType_2218_,
                                            v_a_2236_,
                                            v_a_2245_,
                                            v_a_2253_,
                                        );
                                        v___x_2258_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_elabWFRel_spec__1___redArg(v___x_2257_, v___y_2228_);
                                        v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
                                        lean_inc(v_a_2259_);
                                        lean_dec_ref(v___x_2258_);
                                        v___x_2260_ = lean_apply_8(
                                            v_k_2224_,
                                            v_a_2259_,
                                            v___y_2225_,
                                            v___y_2226_,
                                            v___y_2227_,
                                            v___y_2228_,
                                            v___y_2229_,
                                            v___y_2230_,
                                            lean_box(0),
                                        );
                                        return v___x_2260_;
                                    } else {
                                        lean_dec_ref_known(v___x_2248_, 2);
                                        lean_dec(v_a_2245_);
                                        lean_dec(v_a_2236_);
                                        lean_dec(v_a_2233_);
                                        lean_dec(v___y_2230_);
                                        lean_dec_ref(v___y_2229_);
                                        lean_dec(v___y_2228_);
                                        lean_dec_ref(v___y_2227_);
                                        lean_dec(v___y_2226_);
                                        lean_dec_ref(v___y_2225_);
                                        lean_dec_ref(v_k_2224_);
                                        lean_dec_ref(v_argType_2218_);
                                        v_a_2261_ = lean_ctor_get(v___x_2252_, 0);
                                        v_isSharedCheck_2268_ =
                                            (!lean_is_exclusive(v___x_2252_)) as u8;
                                        if v_isSharedCheck_2268_ == 0 {
                                            v___x_2263_ = v___x_2252_;
                                            v_isShared_2264_ = v_isSharedCheck_2268_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2261_);
                                            lean_dec(v___x_2252_);
                                            v___x_2263_ = lean_box(0);
                                            v_isShared_2264_ = v_isSharedCheck_2268_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2238_);
                                    lean_dec(v_a_2236_);
                                    lean_dec(v_a_2233_);
                                    lean_dec(v___y_2230_);
                                    lean_dec_ref(v___y_2229_);
                                    lean_dec(v___y_2228_);
                                    lean_dec_ref(v___y_2227_);
                                    lean_dec(v___y_2226_);
                                    lean_dec_ref(v___y_2225_);
                                    lean_dec_ref(v_k_2224_);
                                    lean_dec_ref(v_argType_2218_);
                                    v_a_2269_ = lean_ctor_get(v___x_2244_, 0);
                                    v_isSharedCheck_2276_ = (!lean_is_exclusive(v___x_2244_)) as u8;
                                    if v_isSharedCheck_2276_ == 0 {
                                        v___x_2271_ = v___x_2244_;
                                        v_isShared_2272_ = v_isSharedCheck_2276_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2269_);
                                        lean_dec(v___x_2244_);
                                        v___x_2271_ = lean_box(0);
                                        v_isShared_2272_ = v_isSharedCheck_2276_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2238_);
                                lean_dec(v_a_2236_);
                                lean_dec(v_a_2233_);
                                lean_dec(v___y_2230_);
                                lean_dec_ref(v___y_2229_);
                                lean_dec(v___y_2228_);
                                lean_dec_ref(v___y_2227_);
                                lean_dec(v___y_2226_);
                                lean_dec_ref(v___y_2225_);
                                lean_dec_ref(v_k_2224_);
                                lean_dec_ref(v_argsPacker_2219_);
                                lean_dec_ref(v_argType_2218_);
                                v_a_2277_ = lean_ctor_get(v___x_2242_, 0);
                                v_isSharedCheck_2284_ = (!lean_is_exclusive(v___x_2242_)) as u8;
                                if v_isSharedCheck_2284_ == 0 {
                                    v___x_2279_ = v___x_2242_;
                                    v_isShared_2280_ = v_isSharedCheck_2284_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2277_);
                                    lean_dec(v___x_2242_);
                                    v___x_2279_ = lean_box(0);
                                    v_isShared_2280_ = v_isSharedCheck_2284_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2236_);
                            lean_dec(v_a_2233_);
                            lean_dec(v___y_2230_);
                            lean_dec_ref(v___y_2229_);
                            lean_dec(v___y_2228_);
                            lean_dec_ref(v___y_2227_);
                            lean_dec(v___y_2226_);
                            lean_dec_ref(v___y_2225_);
                            lean_dec_ref(v_k_2224_);
                            lean_dec_ref(v_termMeasures_2223_);
                            lean_dec_ref(v_fixedArgs_2222_);
                            lean_dec_ref(v_argsPacker_2219_);
                            lean_dec_ref(v_argType_2218_);
                            v_a_2285_ = lean_ctor_get(v___x_2237_, 0);
                            v_isSharedCheck_2292_ = (!lean_is_exclusive(v___x_2237_)) as u8;
                            if v_isSharedCheck_2292_ == 0 {
                                v___x_2287_ = v___x_2237_;
                                v_isShared_2288_ = v_isSharedCheck_2292_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2285_);
                                lean_dec(v___x_2237_);
                                v___x_2287_ = lean_box(0);
                                v_isShared_2288_ = v_isSharedCheck_2292_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2233_);
                        lean_dec(v___y_2230_);
                        lean_dec_ref(v___y_2229_);
                        lean_dec(v___y_2228_);
                        lean_dec_ref(v___y_2227_);
                        lean_dec(v___y_2226_);
                        lean_dec_ref(v___y_2225_);
                        lean_dec_ref(v_k_2224_);
                        lean_dec_ref(v_termMeasures_2223_);
                        lean_dec_ref(v_fixedArgs_2222_);
                        lean_dec_ref(v_argsPacker_2219_);
                        lean_dec_ref(v_argType_2218_);
                        v_a_2293_ = lean_ctor_get(v___x_2235_, 0);
                        v_isSharedCheck_2300_ = (!lean_is_exclusive(v___x_2235_)) as u8;
                        if v_isSharedCheck_2300_ == 0 {
                            v___x_2295_ = v___x_2235_;
                            v_isShared_2296_ = v_isSharedCheck_2300_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2293_);
                            lean_dec(v___x_2235_);
                            v___x_2295_ = lean_box(0);
                            v_isShared_2296_ = v_isSharedCheck_2300_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2230_);
                    lean_dec_ref(v___y_2229_);
                    lean_dec(v___y_2228_);
                    lean_dec_ref(v___y_2227_);
                    lean_dec(v___y_2226_);
                    lean_dec_ref(v___y_2225_);
                    lean_dec_ref(v_k_2224_);
                    lean_dec_ref(v_termMeasures_2223_);
                    lean_dec_ref(v_fixedArgs_2222_);
                    lean_dec_ref(v_argsPacker_2219_);
                    lean_dec_ref(v_argType_2218_);
                    v_a_2301_ = lean_ctor_get(v___x_2232_, 0);
                    v_isSharedCheck_2308_ = (!lean_is_exclusive(v___x_2232_)) as u8;
                    if v_isSharedCheck_2308_ == 0 {
                        v___x_2303_ = v___x_2232_;
                        v_isShared_2304_ = v_isSharedCheck_2308_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2301_);
                        lean_dec(v___x_2232_);
                        v___x_2303_ = lean_box(0);
                        v_isShared_2304_ = v_isSharedCheck_2308_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2264_ == 0 {
                    v___x_2266_ = v___x_2263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
                    v___x_2266_ = v_reuseFailAlloc_2267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2266_;
            }
            3 => {
                if v_isShared_2272_ == 0 {
                    v___x_2274_ = v___x_2271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
                    v___x_2274_ = v_reuseFailAlloc_2275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2274_;
            }
            5 => {
                if v_isShared_2280_ == 0 {
                    v___x_2282_ = v___x_2279_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
                    v___x_2282_ = v_reuseFailAlloc_2283_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2282_;
            }
            7 => {
                if v_isShared_2288_ == 0 {
                    v___x_2290_ = v___x_2287_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
                    v___x_2290_ = v_reuseFailAlloc_2291_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2290_;
            }
            9 => {
                if v_isShared_2296_ == 0 {
                    v___x_2298_ = v___x_2295_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
                    v___x_2298_ = v_reuseFailAlloc_2299_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2298_;
            }
            11 => {
                if v_isShared_2304_ == 0 {
                    v___x_2306_ = v___x_2303_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
                    v___x_2306_ = v_reuseFailAlloc_2307_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed(
    mut v_argType_2309_: *mut LeanObject,
    mut v_argsPacker_2310_: *mut LeanObject,
    mut v_declNames_2311_: *mut LeanObject,
    mut v_fixedParamPerms_2312_: *mut LeanObject,
    mut v_fixedArgs_2313_: *mut LeanObject,
    mut v_termMeasures_2314_: *mut LeanObject,
    mut v_k_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
    mut v___y_2319_: *mut LeanObject,
    mut v___y_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2323_: *mut LeanObject = core::ptr::null_mut();
    v_res_2323_ = l_Lean_Elab_WF_elabWFRel___redArg___lam__0(
        v_argType_2309_,
        v_argsPacker_2310_,
        v_declNames_2311_,
        v_fixedParamPerms_2312_,
        v_fixedArgs_2313_,
        v_termMeasures_2314_,
        v_k_2315_,
        v___y_2316_,
        v___y_2317_,
        v___y_2318_,
        v___y_2319_,
        v___y_2320_,
        v___y_2321_,
    );
    lean_dec_ref(v_fixedParamPerms_2312_);
    lean_dec_ref(v_declNames_2311_);
    return v_res_2323_;
}
pub unsafe fn l_Lean_Elab_WF_elabWFRel___redArg(
    mut v_declNames_2324_: *mut LeanObject,
    mut v_unaryPreDefName_2325_: *mut LeanObject,
    mut v_fixedParamPerms_2326_: *mut LeanObject,
    mut v_fixedArgs_2327_: *mut LeanObject,
    mut v_argsPacker_2328_: *mut LeanObject,
    mut v_argType_2329_: *mut LeanObject,
    mut v_termMeasures_2330_: *mut LeanObject,
    mut v_k_2331_: *mut LeanObject,
    mut v_a_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
    mut v_a_2334_: *mut LeanObject,
    mut v_a_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
    mut v_a_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    v___f_2339_ = lean_alloc_closure(
        l_Lean_Elab_WF_elabWFRel___redArg___lam__0___boxed as *mut core::ffi::c_void,
        14,
        7,
    );
    lean_closure_set(v___f_2339_, 0, v_argType_2329_);
    lean_closure_set(v___f_2339_, 1, v_argsPacker_2328_);
    lean_closure_set(v___f_2339_, 2, v_declNames_2324_);
    lean_closure_set(v___f_2339_, 3, v_fixedParamPerms_2326_);
    lean_closure_set(v___f_2339_, 4, v_fixedArgs_2327_);
    lean_closure_set(v___f_2339_, 5, v_termMeasures_2330_);
    lean_closure_set(v___f_2339_, 6, v_k_2331_);
    v___x_2340_ = l_Lean_Elab_Term_withDeclName___redArg(
        v_unaryPreDefName_2325_,
        v___f_2339_,
        v_a_2332_,
        v_a_2333_,
        v_a_2334_,
        v_a_2335_,
        v_a_2336_,
        v_a_2337_,
    );
    return v___x_2340_;
}
pub unsafe fn l_Lean_Elab_WF_elabWFRel___redArg___boxed(
    mut v_declNames_2341_: *mut LeanObject,
    mut v_unaryPreDefName_2342_: *mut LeanObject,
    mut v_fixedParamPerms_2343_: *mut LeanObject,
    mut v_fixedArgs_2344_: *mut LeanObject,
    mut v_argsPacker_2345_: *mut LeanObject,
    mut v_argType_2346_: *mut LeanObject,
    mut v_termMeasures_2347_: *mut LeanObject,
    mut v_k_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2356_: *mut LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Lean_Elab_WF_elabWFRel___redArg(
        v_declNames_2341_,
        v_unaryPreDefName_2342_,
        v_fixedParamPerms_2343_,
        v_fixedArgs_2344_,
        v_argsPacker_2345_,
        v_argType_2346_,
        v_termMeasures_2347_,
        v_k_2348_,
        v_a_2349_,
        v_a_2350_,
        v_a_2351_,
        v_a_2352_,
        v_a_2353_,
        v_a_2354_,
    );
    lean_dec(v_a_2354_);
    lean_dec_ref(v_a_2353_);
    lean_dec(v_a_2352_);
    lean_dec_ref(v_a_2351_);
    lean_dec(v_a_2350_);
    lean_dec_ref(v_a_2349_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_Elab_WF_elabWFRel(
    mut v_00_u03b1_2357_: *mut LeanObject,
    mut v_declNames_2358_: *mut LeanObject,
    mut v_unaryPreDefName_2359_: *mut LeanObject,
    mut v_fixedParamPerms_2360_: *mut LeanObject,
    mut v_fixedArgs_2361_: *mut LeanObject,
    mut v_argsPacker_2362_: *mut LeanObject,
    mut v_argType_2363_: *mut LeanObject,
    mut v_termMeasures_2364_: *mut LeanObject,
    mut v_k_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
    mut v_a_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    v___x_2373_ = l_Lean_Elab_WF_elabWFRel___redArg(
        v_declNames_2358_,
        v_unaryPreDefName_2359_,
        v_fixedParamPerms_2360_,
        v_fixedArgs_2361_,
        v_argsPacker_2362_,
        v_argType_2363_,
        v_termMeasures_2364_,
        v_k_2365_,
        v_a_2366_,
        v_a_2367_,
        v_a_2368_,
        v_a_2369_,
        v_a_2370_,
        v_a_2371_,
    );
    return v___x_2373_;
}
pub unsafe fn l_Lean_Elab_WF_elabWFRel___boxed(
    mut v_00_u03b1_2374_: *mut LeanObject,
    mut v_declNames_2375_: *mut LeanObject,
    mut v_unaryPreDefName_2376_: *mut LeanObject,
    mut v_fixedParamPerms_2377_: *mut LeanObject,
    mut v_fixedArgs_2378_: *mut LeanObject,
    mut v_argsPacker_2379_: *mut LeanObject,
    mut v_argType_2380_: *mut LeanObject,
    mut v_termMeasures_2381_: *mut LeanObject,
    mut v_k_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
    mut v_a_2386_: *mut LeanObject,
    mut v_a_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
    mut v_a_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2390_: *mut LeanObject = core::ptr::null_mut();
    v_res_2390_ = l_Lean_Elab_WF_elabWFRel(
        v_00_u03b1_2374_,
        v_declNames_2375_,
        v_unaryPreDefName_2376_,
        v_fixedParamPerms_2377_,
        v_fixedArgs_2378_,
        v_argsPacker_2379_,
        v_argType_2380_,
        v_termMeasures_2381_,
        v_k_2382_,
        v_a_2383_,
        v_a_2384_,
        v_a_2385_,
        v_a_2386_,
        v_a_2387_,
        v_a_2388_,
    );
    lean_dec(v_a_2388_);
    lean_dec_ref(v_a_2387_);
    lean_dec(v_a_2386_);
    lean_dec_ref(v_a_2385_);
    lean_dec(v_a_2384_);
    lean_dec_ref(v_a_2383_);
    return v_res_2390_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0(
    mut v_fixedParamPerms_2391_: *mut LeanObject,
    mut v_fixedArgs_2392_: *mut LeanObject,
    mut v_as_2393_: *mut LeanObject,
    mut v_i_2394_: *mut LeanObject,
    mut v_j_2395_: *mut LeanObject,
    mut v_inv_2396_: *mut LeanObject,
    mut v_bs_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    v___x_2405_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___redArg(
        v_fixedParamPerms_2391_,
        v_fixedArgs_2392_,
        v_as_2393_,
        v_i_2394_,
        v_j_2395_,
        v_bs_2397_,
        v___y_2400_,
        v___y_2401_,
        v___y_2402_,
        v___y_2403_,
    );
    return v___x_2405_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0___boxed(
    mut v_fixedParamPerms_2406_: *mut LeanObject,
    mut v_fixedArgs_2407_: *mut LeanObject,
    mut v_as_2408_: *mut LeanObject,
    mut v_i_2409_: *mut LeanObject,
    mut v_j_2410_: *mut LeanObject,
    mut v_inv_2411_: *mut LeanObject,
    mut v_bs_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2420_: *mut LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_elabWFRel_spec__0(
        v_fixedParamPerms_2406_,
        v_fixedArgs_2407_,
        v_as_2408_,
        v_i_2409_,
        v_j_2410_,
        v_inv_2411_,
        v_bs_2412_,
        v___y_2413_,
        v___y_2414_,
        v___y_2415_,
        v___y_2416_,
        v___y_2417_,
        v___y_2418_,
    );
    lean_dec(v___y_2418_);
    lean_dec_ref(v___y_2417_);
    lean_dec(v___y_2416_);
    lean_dec_ref(v___y_2415_);
    lean_dec(v___y_2414_);
    lean_dec_ref(v___y_2413_);
    lean_dec_ref(v_as_2408_);
    lean_dec_ref(v_fixedParamPerms_2406_);
    return v_res_2420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_WF_Rel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Rename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ArgsPacker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
}
