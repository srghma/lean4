// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProveEq
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Util Lean.Meta.Tactic.Grind.Simp
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_grind_internalize,
    lean_grind_mk_eq_proof, lean_grind_mk_heq_proof, lean_grind_process_new_facts, lean_infer_type,
    lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_mix_hash, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_mkAppB, l_Lean_mkAppN,
    l_Lean_mkBVar, l_Lean_mkForall, l_Lean_mkLambda,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_alreadyInternalized___redArg,
    l_Lean_Meta_Grind_hasSameType, l_Lean_Meta_Grind_isEqv___redArg,
    l_Lean_Meta_Grind_withoutModifyingState___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,7699194985028780469 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 98, 115, 116, 114, 97, 99, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value) as *mut crate::leanh::LeanObject,17040932255416921605 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 111, 118, 101, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value) as *mut crate::leanh::LeanObject,6936347780346814288 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 98, 115, 116, 114, 97, 99, 116, 58, 32, 40, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [41, 32, 61, 32, 40, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_proveEq_x3f___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Meta_Grind_proveEq_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_proveEq_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_proveEq_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_proveEq_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(
    mut v_e_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_unused_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1911_ = l_Lean_Expr_hasMVar(v_e_1908_);
                if v___x_1911_ == 0 {
                    v___x_1912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1912_, 0, v_e_1908_);
                    return v___x_1912_;
                } else {
                    v___x_1913_ = lean_st_ref_get(v___y_1909_);
                    v_mctx_1914_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1914_);
                    crate::leanh::lean_dec(v___x_1913_);
                    v___x_1915_ = l_Lean_instantiateMVarsCore(v_mctx_1914_, v_e_1908_);
                    v_fst_1916_ = crate::leanh::lean_ctor_get(v___x_1915_, 0);
                    crate::leanh::lean_inc(v_fst_1916_);
                    v_snd_1917_ = crate::leanh::lean_ctor_get(v___x_1915_, 1);
                    crate::leanh::lean_inc(v_snd_1917_);
                    crate::leanh::lean_dec_ref(v___x_1915_);
                    v___x_1918_ = lean_st_ref_take(v___y_1909_);
                    v_cache_1919_ = crate::leanh::lean_ctor_get(v___x_1918_, 1);
                    v_zetaDeltaFVarIds_1920_ = crate::leanh::lean_ctor_get(v___x_1918_, 2);
                    v_postponed_1921_ = crate::leanh::lean_ctor_get(v___x_1918_, 3);
                    v_diag_1922_ = crate::leanh::lean_ctor_get(v___x_1918_, 4);
                    v_isSharedCheck_1931_ = (!crate::leanh::lean_is_exclusive(v___x_1918_)) as u8;
                    if v_isSharedCheck_1931_ == 0 {
                        v_unused_1932_ = crate::leanh::lean_ctor_get(v___x_1918_, 0);
                        crate::leanh::lean_dec(v_unused_1932_);
                        v___x_1924_ = v___x_1918_;
                        v_isShared_1925_ = v_isSharedCheck_1931_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1922_);
                        crate::leanh::lean_inc(v_postponed_1921_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1920_);
                        crate::leanh::lean_inc(v_cache_1919_);
                        crate::leanh::lean_dec(v___x_1918_);
                        v___x_1924_ = crate::leanh::lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1924_, 0, v_snd_1917_);
                    v___x_1927_ = v___x_1924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_snd_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_cache_1919_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1930_,
                        2,
                        v_zetaDeltaFVarIds_1920_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_postponed_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_diag_1922_);
                    v___x_1927_ = v_reuseFailAlloc_1930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1928_ = lean_st_ref_set(v___y_1909_, v___x_1927_);
                v___x_1929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1929_, 0, v_fst_1916_);
                return v___x_1929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(
    mut v_e_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1936_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1933_, v___y_1934_);
    crate::leanh::lean_dec(v___y_1934_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(
    mut v_e_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1937_, v___y_1945_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(
    mut v_e_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(v_e_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
    crate::leanh::lean_dec(v___y_1960_);
    crate::leanh::lean_dec_ref(v___y_1959_);
    crate::leanh::lean_dec(v___y_1958_);
    crate::leanh::lean_dec_ref(v___y_1957_);
    crate::leanh::lean_dec(v___y_1956_);
    crate::leanh::lean_dec_ref(v___y_1955_);
    crate::leanh::lean_dec(v___y_1954_);
    crate::leanh::lean_dec_ref(v___y_1953_);
    crate::leanh::lean_dec(v___y_1952_);
    crate::leanh::lean_dec(v___y_1951_);
    return v_res_1962_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(
    mut v_e_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
    mut v_a_1965_: *mut crate::leanh::LeanObject,
    mut v_a_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut v_unused_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_a_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1975_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1963_, v_a_1964_);
                if crate::leanh::lean_obj_tag(v___x_1975_) == 0 {
                    v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2007_ = (!crate::leanh::lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2007_ == 0 {
                        v___x_1978_ = v___x_1975_;
                        v_isShared_1979_ = v_isSharedCheck_2007_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1976_);
                        crate::leanh::lean_dec(v___x_1975_);
                        v___x_1978_ = crate::leanh::lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_2007_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1963_);
                    v_a_2008_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2015_ = (!crate::leanh::lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v___x_2010_ = v___x_1975_;
                        v_isShared_2011_ = v_isSharedCheck_2015_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2008_);
                        crate::leanh::lean_dec(v___x_1975_);
                        v___x_2010_ = crate::leanh::lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2015_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1980_ = (crate::leanh::lean_unbox(v_a_1976_) as u8);
                crate::leanh::lean_dec(v_a_1976_);
                if v___x_1980_ == 0 {
                    crate::leanh::lean_del_object(v___x_1978_);
                    v___x_1981_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1963_, v_a_1971_);
                    v_a_1982_ = crate::leanh::lean_ctor_get(v___x_1981_, 0);
                    crate::leanh::lean_inc(v_a_1982_);
                    crate::leanh::lean_dec_ref(v___x_1981_);
                    v___x_1983_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                        v_a_1982_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_,
                        v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1983_) == 0 {
                        v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1983_, 0);
                        crate::leanh::lean_inc_n(v_a_1984_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1983_, 1);
                        v___x_1985_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1986_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_1973_);
                        crate::leanh::lean_inc_ref(v_a_1972_);
                        crate::leanh::lean_inc(v_a_1971_);
                        crate::leanh::lean_inc_ref(v_a_1970_);
                        crate::leanh::lean_inc(v_a_1969_);
                        crate::leanh::lean_inc_ref(v_a_1968_);
                        crate::leanh::lean_inc(v_a_1967_);
                        crate::leanh::lean_inc_ref(v_a_1966_);
                        crate::leanh::lean_inc(v_a_1965_);
                        crate::leanh::lean_inc(v_a_1964_);
                        v___x_1987_ = lean_grind_internalize(
                            v_a_1984_,
                            v___x_1985_,
                            v___x_1986_,
                            v_a_1964_,
                            v_a_1965_,
                            v_a_1966_,
                            v_a_1967_,
                            v_a_1968_,
                            v_a_1969_,
                            v_a_1970_,
                            v_a_1971_,
                            v_a_1972_,
                            v_a_1973_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1987_) == 0 {
                            v_isSharedCheck_1994_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1987_)) as u8;
                            if v_isSharedCheck_1994_ == 0 {
                                v_unused_1995_ = crate::leanh::lean_ctor_get(v___x_1987_, 0);
                                crate::leanh::lean_dec(v_unused_1995_);
                                v___x_1989_ = v___x_1987_;
                                v_isShared_1990_ = v_isSharedCheck_1994_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1987_);
                                v___x_1989_ = crate::leanh::lean_box(0);
                                v_isShared_1990_ = v_isSharedCheck_1994_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1984_);
                            v_a_1996_ = crate::leanh::lean_ctor_get(v___x_1987_, 0);
                            v_isSharedCheck_2003_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1987_)) as u8;
                            if v_isSharedCheck_2003_ == 0 {
                                v___x_1998_ = v___x_1987_;
                                v_isShared_1999_ = v_isSharedCheck_2003_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1996_);
                                crate::leanh::lean_dec(v___x_1987_);
                                v___x_1998_ = crate::leanh::lean_box(0);
                                v_isShared_1999_ = v_isSharedCheck_2003_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        return v___x_1983_;
                    }
                } else {
                    if v_isShared_1979_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1978_, 0, v_e_1963_);
                        v___x_2005_ = v___x_1978_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_e_1963_);
                        v___x_2005_ = v_reuseFailAlloc_2006_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1989_, 0, v_a_1984_);
                    v___x_1992_ = v___x_1989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1984_);
                    v___x_1992_ = v_reuseFailAlloc_1993_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1992_;
            }
            4 => {
                if v_isShared_1999_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2001_;
            }
            6 => {
                return v___x_2005_;
            }
            7 => {
                if v_isShared_2011_ == 0 {
                    v___x_2013_ = v___x_2010_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized___boxed(
    mut v_e_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
    mut v_a_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(
        v_e_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_,
        v_a_2024_, v_a_2025_, v_a_2026_,
    );
    crate::leanh::lean_dec(v_a_2026_);
    crate::leanh::lean_dec_ref(v_a_2025_);
    crate::leanh::lean_dec(v_a_2024_);
    crate::leanh::lean_dec_ref(v_a_2023_);
    crate::leanh::lean_dec(v_a_2022_);
    crate::leanh::lean_dec_ref(v_a_2021_);
    crate::leanh::lean_dec(v_a_2020_);
    crate::leanh::lean_dec_ref(v_a_2019_);
    crate::leanh::lean_dec(v_a_2018_);
    crate::leanh::lean_dec(v_a_2017_);
    return v_res_2028_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
    mut v_a_2029_: *mut crate::leanh::LeanObject,
    mut v_a_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2032_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2033_ = lean_nat_dec_lt(v___x_2032_, v_a_2029_);
    v___x_2034_ = crate::leanh::lean_box((v___x_2033_) as usize);
    v___x_2035_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2035_, 0, v___x_2034_);
    crate::leanh::lean_ctor_set(v___x_2035_, 1, v_a_2030_);
    v___x_2036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2036_, 0, v___x_2035_);
    v___x_2037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2041_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
        v_a_2038_, v_a_2039_,
    );
    crate::leanh::lean_dec(v_a_2038_);
    return v_res_2041_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(
    mut v_a_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
    mut v_a_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
        v_a_2042_, v_a_2043_,
    );
    return v___x_2055_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(
        v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_,
        v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_,
    );
    crate::leanh::lean_dec(v_a_2067_);
    crate::leanh::lean_dec_ref(v_a_2066_);
    crate::leanh::lean_dec(v_a_2065_);
    crate::leanh::lean_dec_ref(v_a_2064_);
    crate::leanh::lean_dec(v_a_2063_);
    crate::leanh::lean_dec_ref(v_a_2062_);
    crate::leanh::lean_dec(v_a_2061_);
    crate::leanh::lean_dec_ref(v_a_2060_);
    crate::leanh::lean_dec(v_a_2059_);
    crate::leanh::lean_dec(v_a_2058_);
    crate::leanh::lean_dec(v_a_2056_);
    return v_res_2069_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(
    mut v_x_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2085_ = lean_nat_add(v_a_2071_, v___x_2084_);
    crate::leanh::lean_inc(v_a_2082_);
    crate::leanh::lean_inc_ref(v_a_2081_);
    crate::leanh::lean_inc(v_a_2080_);
    crate::leanh::lean_inc_ref(v_a_2079_);
    crate::leanh::lean_inc(v_a_2078_);
    crate::leanh::lean_inc_ref(v_a_2077_);
    crate::leanh::lean_inc(v_a_2076_);
    crate::leanh::lean_inc_ref(v_a_2075_);
    crate::leanh::lean_inc(v_a_2074_);
    crate::leanh::lean_inc(v_a_2073_);
    v___x_2086_ = crate::leanh::lean_apply_13(
        v_x_2070_,
        v___x_2085_,
        v_a_2072_,
        v_a_2073_,
        v_a_2074_,
        v_a_2075_,
        v_a_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
        crate::leanh::lean_box(0),
    );
    return v___x_2086_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(
    mut v_x_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
    mut v_a_2090_: *mut crate::leanh::LeanObject,
    mut v_a_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_a_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ =
        l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(
            v_x_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_,
            v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_,
        );
    crate::leanh::lean_dec(v_a_2099_);
    crate::leanh::lean_dec_ref(v_a_2098_);
    crate::leanh::lean_dec(v_a_2097_);
    crate::leanh::lean_dec_ref(v_a_2096_);
    crate::leanh::lean_dec(v_a_2095_);
    crate::leanh::lean_dec_ref(v_a_2094_);
    crate::leanh::lean_dec(v_a_2093_);
    crate::leanh::lean_dec_ref(v_a_2092_);
    crate::leanh::lean_dec(v_a_2091_);
    crate::leanh::lean_dec(v_a_2090_);
    crate::leanh::lean_dec(v_a_2088_);
    return v_res_2101_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(
    mut v_00_u03b1_2102_: *mut crate::leanh::LeanObject,
    mut v_x_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
    mut v_a_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2118_ = lean_nat_add(v_a_2104_, v___x_2117_);
    crate::leanh::lean_inc(v_a_2115_);
    crate::leanh::lean_inc_ref(v_a_2114_);
    crate::leanh::lean_inc(v_a_2113_);
    crate::leanh::lean_inc_ref(v_a_2112_);
    crate::leanh::lean_inc(v_a_2111_);
    crate::leanh::lean_inc_ref(v_a_2110_);
    crate::leanh::lean_inc(v_a_2109_);
    crate::leanh::lean_inc_ref(v_a_2108_);
    crate::leanh::lean_inc(v_a_2107_);
    crate::leanh::lean_inc(v_a_2106_);
    v___x_2119_ = crate::leanh::lean_apply_13(
        v_x_2103_,
        v___x_2118_,
        v_a_2105_,
        v_a_2106_,
        v_a_2107_,
        v_a_2108_,
        v_a_2109_,
        v_a_2110_,
        v_a_2111_,
        v_a_2112_,
        v_a_2113_,
        v_a_2114_,
        v_a_2115_,
        crate::leanh::lean_box(0),
    );
    return v___x_2119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(
    mut v_00_u03b1_2120_: *mut crate::leanh::LeanObject,
    mut v_x_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: *mut crate::leanh::LeanObject,
    mut v_a_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
    mut v_a_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2135_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(
        v_00_u03b1_2120_,
        v_x_2121_,
        v_a_2122_,
        v_a_2123_,
        v_a_2124_,
        v_a_2125_,
        v_a_2126_,
        v_a_2127_,
        v_a_2128_,
        v_a_2129_,
        v_a_2130_,
        v_a_2131_,
        v_a_2132_,
        v_a_2133_,
    );
    crate::leanh::lean_dec(v_a_2133_);
    crate::leanh::lean_dec_ref(v_a_2132_);
    crate::leanh::lean_dec(v_a_2131_);
    crate::leanh::lean_dec_ref(v_a_2130_);
    crate::leanh::lean_dec(v_a_2129_);
    crate::leanh::lean_dec_ref(v_a_2128_);
    crate::leanh::lean_dec(v_a_2127_);
    crate::leanh::lean_dec_ref(v_a_2126_);
    crate::leanh::lean_dec(v_a_2125_);
    crate::leanh::lean_dec(v_a_2124_);
    crate::leanh::lean_dec(v_a_2122_);
    return v_res_2135_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_i_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_2139_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1;
    v___x_2141_ = lean_name_append_index_after(v___x_2140_, v_i_2139_);
    return v___x_2141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(
    mut v_as_2142_: *mut crate::leanh::LeanObject,
    mut v_sz_2143_: usize,
    mut v_i_2144_: usize,
    mut v_b_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: u8 = 0;
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2146_ = lean_usize_dec_lt(v_i_2144_, v_sz_2143_);
                if v___x_2146_ == 0 {
                    return v_b_2145_;
                } else {
                    v_a_2147_ = lean_array_uget_borrowed(v_as_2142_, v_i_2144_);
                    v___x_2148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2);
                    v___x_2149_ = 0;
                    crate::leanh::lean_inc(v_a_2147_);
                    v___x_2150_ = l_Lean_mkLambda(v___x_2148_, v___x_2149_, v_a_2147_, v_b_2145_);
                    v___x_2151_ = 1usize;
                    v___x_2152_ = lean_usize_add(v_i_2144_, v___x_2151_);
                    v_i_2144_ = v___x_2152_;
                    v_b_2145_ = v___x_2150_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___boxed(
    mut v_as_2154_: *mut crate::leanh::LeanObject,
    mut v_sz_2155_: *mut crate::leanh::LeanObject,
    mut v_i_2156_: *mut crate::leanh::LeanObject,
    mut v_b_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2158_: usize = 0;
    let mut v_i_boxed_2159_: usize = 0;
    let mut v_res_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2158_ = crate::leanh::lean_unbox_usize(v_sz_2155_);
    crate::leanh::lean_dec(v_sz_2155_);
    v_i_boxed_2159_ = crate::leanh::lean_unbox_usize(v_i_2156_);
    crate::leanh::lean_dec(v_i_2156_);
    v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_as_2154_, v_sz_boxed_2158_, v_i_boxed_2159_, v_b_2157_);
    crate::leanh::lean_dec_ref(v_as_2154_);
    return v_res_2160_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(
    mut v_varTypes_2161_: *mut crate::leanh::LeanObject,
    mut v_b_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2163_: usize = 0;
    let mut v___x_2164_: usize = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_2163_ = lean_array_size(v_varTypes_2161_);
    v___x_2164_ = 0usize;
    v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_varTypes_2161_, v_sz_2163_, v___x_2164_, v_b_2162_);
    return v___x_2165_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(
    mut v_varTypes_2166_: *mut crate::leanh::LeanObject,
    mut v_b_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ =
        l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(
            v_varTypes_2166_,
            v_b_2167_,
        );
    crate::leanh::lean_dec_ref(v_varTypes_2166_);
    return v_res_2168_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_x_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: u8 = 0;
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2170_) == 0 {
                    v___x_2171_ = crate::leanh::lean_box(0);
                    return v___x_2171_;
                } else {
                    v_key_2172_ = crate::leanh::lean_ctor_get(v_x_2170_, 0);
                    v_value_2173_ = crate::leanh::lean_ctor_get(v_x_2170_, 1);
                    v_tail_2174_ = crate::leanh::lean_ctor_get(v_x_2170_, 2);
                    v_fst_2179_ = crate::leanh::lean_ctor_get(v_key_2172_, 0);
                    v_snd_2180_ = crate::leanh::lean_ctor_get(v_key_2172_, 1);
                    v_fst_2181_ = crate::leanh::lean_ctor_get(v_a_2169_, 0);
                    v_snd_2182_ = crate::leanh::lean_ctor_get(v_a_2169_, 1);
                    v___x_2183_ = lean_expr_eqv(v_fst_2179_, v_fst_2181_);
                    if v___x_2183_ == 0 {
                        v___y_2176_ = v___x_2183_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2184_ = lean_expr_eqv(v_snd_2180_, v_snd_2182_);
                        v___y_2176_ = v___x_2184_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2176_ == 0 {
                    v_x_2170_ = v_tail_2174_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_2173_);
                    v___x_2178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2178_, 0, v_value_2173_);
                    return v___x_2178_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_x_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_2185_, v_x_2186_);
    crate::leanh::lean_dec(v_x_2186_);
    crate::leanh::lean_dec_ref(v_a_2185_);
    return v_res_2187_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(
    mut v_m_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u64 = 0;
    let mut v___x_2195_: u64 = 0;
    let mut v___x_2196_: u64 = 0;
    let mut v___x_2197_: u64 = 0;
    let mut v___x_2198_: u64 = 0;
    let mut v_fold_2199_: u64 = 0;
    let mut v___x_2200_: u64 = 0;
    let mut v___x_2201_: u64 = 0;
    let mut v___x_2202_: u64 = 0;
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: usize = 0;
    let mut v___x_2207_: usize = 0;
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2190_ = crate::leanh::lean_ctor_get(v_m_2188_, 1);
    v_fst_2191_ = crate::leanh::lean_ctor_get(v_a_2189_, 0);
    v_snd_2192_ = crate::leanh::lean_ctor_get(v_a_2189_, 1);
    v___x_2193_ = lean_array_get_size(v_buckets_2190_);
    v___x_2194_ = l_Lean_Expr_hash(v_fst_2191_);
    v___x_2195_ = l_Lean_Expr_hash(v_snd_2192_);
    v___x_2196_ = lean_uint64_mix_hash(v___x_2194_, v___x_2195_);
    v___x_2197_ = 32u64;
    v___x_2198_ = lean_uint64_shift_right(v___x_2196_, v___x_2197_);
    v_fold_2199_ = lean_uint64_xor(v___x_2196_, v___x_2198_);
    v___x_2200_ = 16u64;
    v___x_2201_ = lean_uint64_shift_right(v_fold_2199_, v___x_2200_);
    v___x_2202_ = lean_uint64_xor(v_fold_2199_, v___x_2201_);
    v___x_2203_ = lean_uint64_to_usize(v___x_2202_);
    v___x_2204_ = lean_usize_of_nat(v___x_2193_);
    v___x_2205_ = 1usize;
    v___x_2206_ = lean_usize_sub(v___x_2204_, v___x_2205_);
    v___x_2207_ = lean_usize_land(v___x_2203_, v___x_2206_);
    v___x_2208_ = lean_array_uget_borrowed(v_buckets_2190_, v___x_2207_);
    v___x_2209_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_2189_, v___x_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg___boxed(
    mut v_m_2210_: *mut crate::leanh::LeanObject,
    mut v_a_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_2210_, v_a_2211_);
    crate::leanh::lean_dec_ref(v_a_2211_);
    crate::leanh::lean_dec_ref(v_m_2210_);
    return v_res_2212_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_x_2214_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2215_: u8 = 0;
    let mut v_key_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: u8 = 0;
    let mut v_fst_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2214_) == 0 {
                    v___x_2215_ = 0;
                    return v___x_2215_;
                } else {
                    v_key_2216_ = crate::leanh::lean_ctor_get(v_x_2214_, 0);
                    v_tail_2217_ = crate::leanh::lean_ctor_get(v_x_2214_, 2);
                    v_fst_2221_ = crate::leanh::lean_ctor_get(v_key_2216_, 0);
                    v_snd_2222_ = crate::leanh::lean_ctor_get(v_key_2216_, 1);
                    v_fst_2223_ = crate::leanh::lean_ctor_get(v_a_2213_, 0);
                    v_snd_2224_ = crate::leanh::lean_ctor_get(v_a_2213_, 1);
                    v___x_2225_ = lean_expr_eqv(v_fst_2221_, v_fst_2223_);
                    if v___x_2225_ == 0 {
                        v___y_2219_ = v___x_2225_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2226_ = lean_expr_eqv(v_snd_2222_, v_snd_2224_);
                        v___y_2219_ = v___x_2226_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2219_ == 0 {
                    v_x_2214_ = v_tail_2217_;
                    state = 0;
                    continue;
                } else {
                    return v___y_2219_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg___boxed(
    mut v_a_2227_: *mut crate::leanh::LeanObject,
    mut v_x_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2229_: u8 = 0;
    let mut v_r_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_2227_, v_x_2228_);
    crate::leanh::lean_dec(v_x_2228_);
    crate::leanh::lean_dec_ref(v_a_2227_);
    v_r_2230_ = crate::leanh::lean_box((v_res_2229_) as usize);
    return v_r_2230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(
    mut v_a_2231_: *mut crate::leanh::LeanObject,
    mut v_b_2232_: *mut crate::leanh::LeanObject,
    mut v_x_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2239_: u8 = 0;
    let mut v___y_2241_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: u8 = 0;
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2233_) == 0 {
                    crate::leanh::lean_dec(v_b_2232_);
                    crate::leanh::lean_dec_ref(v_a_2231_);
                    return v_x_2233_;
                } else {
                    v_key_2234_ = crate::leanh::lean_ctor_get(v_x_2233_, 0);
                    v_value_2235_ = crate::leanh::lean_ctor_get(v_x_2233_, 1);
                    v_tail_2236_ = crate::leanh::lean_ctor_get(v_x_2233_, 2);
                    v_isSharedCheck_2255_ = (!crate::leanh::lean_is_exclusive(v_x_2233_)) as u8;
                    if v_isSharedCheck_2255_ == 0 {
                        v___x_2238_ = v_x_2233_;
                        v_isShared_2239_ = v_isSharedCheck_2255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2236_);
                        crate::leanh::lean_inc(v_value_2235_);
                        crate::leanh::lean_inc(v_key_2234_);
                        crate::leanh::lean_dec(v_x_2233_);
                        v___x_2238_ = crate::leanh::lean_box(0);
                        v_isShared_2239_ = v_isSharedCheck_2255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2249_ = crate::leanh::lean_ctor_get(v_key_2234_, 0);
                v_snd_2250_ = crate::leanh::lean_ctor_get(v_key_2234_, 1);
                v_fst_2251_ = crate::leanh::lean_ctor_get(v_a_2231_, 0);
                v_snd_2252_ = crate::leanh::lean_ctor_get(v_a_2231_, 1);
                v___x_2253_ = lean_expr_eqv(v_fst_2249_, v_fst_2251_);
                if v___x_2253_ == 0 {
                    v___y_2241_ = v___x_2253_;
                    state = 2;
                    continue;
                } else {
                    v___x_2254_ = lean_expr_eqv(v_snd_2250_, v_snd_2252_);
                    v___y_2241_ = v___x_2254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_2241_ == 0 {
                    v___x_2242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_2231_, v_b_2232_, v_tail_2236_);
                    if v_isShared_2239_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2238_, 2, v___x_2242_);
                        v___x_2244_ = v___x_2238_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_key_2234_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_value_2235_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 2, v___x_2242_);
                        v___x_2244_ = v_reuseFailAlloc_2245_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2235_);
                    crate::leanh::lean_dec(v_key_2234_);
                    if v_isShared_2239_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2238_, 1, v_b_2232_);
                        crate::leanh::lean_ctor_set(v___x_2238_, 0, v_a_2231_);
                        v___x_2247_ = v___x_2238_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2231_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_b_2232_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_tail_2236_);
                        v___x_2247_ = v_reuseFailAlloc_2248_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2244_;
            }
            4 => {
                return v___x_2247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_2256_: *mut crate::leanh::LeanObject,
    mut v_x_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2263_: u8 = 0;
    let mut v_fst_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u64 = 0;
    let mut v___x_2268_: u64 = 0;
    let mut v___x_2269_: u64 = 0;
    let mut v___x_2270_: u64 = 0;
    let mut v___x_2271_: u64 = 0;
    let mut v_fold_2272_: u64 = 0;
    let mut v___x_2273_: u64 = 0;
    let mut v___x_2274_: u64 = 0;
    let mut v___x_2275_: u64 = 0;
    let mut v___x_2276_: usize = 0;
    let mut v___x_2277_: usize = 0;
    let mut v___x_2278_: usize = 0;
    let mut v___x_2279_: usize = 0;
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2257_) == 0 {
                    return v_x_2256_;
                } else {
                    v_key_2258_ = crate::leanh::lean_ctor_get(v_x_2257_, 0);
                    v_value_2259_ = crate::leanh::lean_ctor_get(v_x_2257_, 1);
                    v_tail_2260_ = crate::leanh::lean_ctor_get(v_x_2257_, 2);
                    v_isSharedCheck_2287_ = (!crate::leanh::lean_is_exclusive(v_x_2257_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2262_ = v_x_2257_;
                        v_isShared_2263_ = v_isSharedCheck_2287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2260_);
                        crate::leanh::lean_inc(v_value_2259_);
                        crate::leanh::lean_inc(v_key_2258_);
                        crate::leanh::lean_dec(v_x_2257_);
                        v___x_2262_ = crate::leanh::lean_box(0);
                        v_isShared_2263_ = v_isSharedCheck_2287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2264_ = crate::leanh::lean_ctor_get(v_key_2258_, 0);
                v_snd_2265_ = crate::leanh::lean_ctor_get(v_key_2258_, 1);
                v___x_2266_ = lean_array_get_size(v_x_2256_);
                v___x_2267_ = l_Lean_Expr_hash(v_fst_2264_);
                v___x_2268_ = l_Lean_Expr_hash(v_snd_2265_);
                v___x_2269_ = lean_uint64_mix_hash(v___x_2267_, v___x_2268_);
                v___x_2270_ = 32u64;
                v___x_2271_ = lean_uint64_shift_right(v___x_2269_, v___x_2270_);
                v_fold_2272_ = lean_uint64_xor(v___x_2269_, v___x_2271_);
                v___x_2273_ = 16u64;
                v___x_2274_ = lean_uint64_shift_right(v_fold_2272_, v___x_2273_);
                v___x_2275_ = lean_uint64_xor(v_fold_2272_, v___x_2274_);
                v___x_2276_ = lean_uint64_to_usize(v___x_2275_);
                v___x_2277_ = lean_usize_of_nat(v___x_2266_);
                v___x_2278_ = 1usize;
                v___x_2279_ = lean_usize_sub(v___x_2277_, v___x_2278_);
                v___x_2280_ = lean_usize_land(v___x_2276_, v___x_2279_);
                v___x_2281_ = lean_array_uget_borrowed(v_x_2256_, v___x_2280_);
                crate::leanh::lean_inc(v___x_2281_);
                if v_isShared_2263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2262_, 2, v___x_2281_);
                    v___x_2283_ = v___x_2262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_key_2258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_value_2259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 2, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2284_ = lean_array_uset(v_x_2256_, v___x_2280_, v___x_2283_);
                v_x_2256_ = v___x_2284_;
                v_x_2257_ = v_tail_2260_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(
    mut v_i_2288_: *mut crate::leanh::LeanObject,
    mut v_source_2289_: *mut crate::leanh::LeanObject,
    mut v_target_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v_es_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2291_ = lean_array_get_size(v_source_2289_);
                v___x_2292_ = lean_nat_dec_lt(v_i_2288_, v___x_2291_);
                if v___x_2292_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2289_);
                    crate::leanh::lean_dec(v_i_2288_);
                    return v_target_2290_;
                } else {
                    v_es_2293_ = lean_array_fget(v_source_2289_, v_i_2288_);
                    v___x_2294_ = crate::leanh::lean_box(0);
                    v_source_2295_ = lean_array_fset(v_source_2289_, v_i_2288_, v___x_2294_);
                    v_target_2296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_target_2290_, v_es_2293_);
                    v___x_2297_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2298_ = lean_nat_add(v_i_2288_, v___x_2297_);
                    crate::leanh::lean_dec(v_i_2288_);
                    v_i_2288_ = v___x_2298_;
                    v_source_2289_ = v_source_2295_;
                    v_target_2290_ = v_target_2296_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(
    mut v_data_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = lean_array_get_size(v_data_2300_);
    v___x_2302_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2303_ = lean_nat_mul(v___x_2301_, v___x_2302_);
    v___x_2304_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2305_ = crate::leanh::lean_box(0);
    v___x_2306_ = lean_mk_array(v_nbuckets_2303_, v___x_2305_);
    v___x_2307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v___x_2304_, v_data_2300_, v___x_2306_);
    return v___x_2307_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(
    mut v_m_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_b_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v_fst_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u64 = 0;
    let mut v___x_2320_: u64 = 0;
    let mut v___x_2321_: u64 = 0;
    let mut v___x_2322_: u64 = 0;
    let mut v___x_2323_: u64 = 0;
    let mut v_fold_2324_: u64 = 0;
    let mut v___x_2325_: u64 = 0;
    let mut v___x_2326_: u64 = 0;
    let mut v___x_2327_: u64 = 0;
    let mut v___x_2328_: usize = 0;
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut v___x_2331_: usize = 0;
    let mut v___x_2332_: usize = 0;
    let mut v_bkt_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: u8 = 0;
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v_val_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2311_ = crate::leanh::lean_ctor_get(v_m_2308_, 0);
                v_buckets_2312_ = crate::leanh::lean_ctor_get(v_m_2308_, 1);
                v_isSharedCheck_2359_ = (!crate::leanh::lean_is_exclusive(v_m_2308_)) as u8;
                if v_isSharedCheck_2359_ == 0 {
                    v___x_2314_ = v_m_2308_;
                    v_isShared_2315_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2312_);
                    crate::leanh::lean_inc(v_size_2311_);
                    crate::leanh::lean_dec(v_m_2308_);
                    v___x_2314_ = crate::leanh::lean_box(0);
                    v_isShared_2315_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2316_ = crate::leanh::lean_ctor_get(v_a_2309_, 0);
                v_snd_2317_ = crate::leanh::lean_ctor_get(v_a_2309_, 1);
                v___x_2318_ = lean_array_get_size(v_buckets_2312_);
                v___x_2319_ = l_Lean_Expr_hash(v_fst_2316_);
                v___x_2320_ = l_Lean_Expr_hash(v_snd_2317_);
                v___x_2321_ = lean_uint64_mix_hash(v___x_2319_, v___x_2320_);
                v___x_2322_ = 32u64;
                v___x_2323_ = lean_uint64_shift_right(v___x_2321_, v___x_2322_);
                v_fold_2324_ = lean_uint64_xor(v___x_2321_, v___x_2323_);
                v___x_2325_ = 16u64;
                v___x_2326_ = lean_uint64_shift_right(v_fold_2324_, v___x_2325_);
                v___x_2327_ = lean_uint64_xor(v_fold_2324_, v___x_2326_);
                v___x_2328_ = lean_uint64_to_usize(v___x_2327_);
                v___x_2329_ = lean_usize_of_nat(v___x_2318_);
                v___x_2330_ = 1usize;
                v___x_2331_ = lean_usize_sub(v___x_2329_, v___x_2330_);
                v___x_2332_ = lean_usize_land(v___x_2328_, v___x_2331_);
                v_bkt_2333_ = lean_array_uget_borrowed(v_buckets_2312_, v___x_2332_);
                v___x_2334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_2309_, v_bkt_2333_);
                if v___x_2334_ == 0 {
                    v___x_2335_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2336_ = lean_nat_add(v_size_2311_, v___x_2335_);
                    crate::leanh::lean_dec(v_size_2311_);
                    crate::leanh::lean_inc(v_bkt_2333_);
                    v___x_2337_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2337_, 0, v_a_2309_);
                    crate::leanh::lean_ctor_set(v___x_2337_, 1, v_b_2310_);
                    crate::leanh::lean_ctor_set(v___x_2337_, 2, v_bkt_2333_);
                    v_buckets_x27_2338_ =
                        lean_array_uset(v_buckets_2312_, v___x_2332_, v___x_2337_);
                    v___x_2339_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2340_ = lean_nat_mul(v_size_x27_2336_, v___x_2339_);
                    v___x_2341_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2342_ = lean_nat_div(v___x_2340_, v___x_2341_);
                    crate::leanh::lean_dec(v___x_2340_);
                    v___x_2343_ = lean_array_get_size(v_buckets_x27_2338_);
                    v___x_2344_ = lean_nat_dec_le(v___x_2342_, v___x_2343_);
                    crate::leanh::lean_dec(v___x_2342_);
                    if v___x_2344_ == 0 {
                        v_val_2345_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_buckets_x27_2338_);
                        if v_isShared_2315_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2314_, 1, v_val_2345_);
                            crate::leanh::lean_ctor_set(v___x_2314_, 0, v_size_x27_2336_);
                            v___x_2347_ = v___x_2314_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2348_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2348_,
                                0,
                                v_size_x27_2336_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_val_2345_);
                            v___x_2347_ = v_reuseFailAlloc_2348_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2315_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2338_);
                            crate::leanh::lean_ctor_set(v___x_2314_, 0, v_size_x27_2336_);
                            v___x_2350_ = v___x_2314_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2351_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2351_,
                                0,
                                v_size_x27_2336_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2351_,
                                1,
                                v_buckets_x27_2338_,
                            );
                            v___x_2350_ = v_reuseFailAlloc_2351_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2333_);
                    v___x_2352_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2353_ =
                        lean_array_uset(v_buckets_2312_, v___x_2332_, v___x_2352_);
                    v___x_2354_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_2309_, v_b_2310_, v_bkt_2333_);
                    v___x_2355_ = lean_array_uset(v_buckets_x27_2353_, v___x_2332_, v___x_2354_);
                    if v_isShared_2315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2314_, 1, v___x_2355_);
                        v___x_2357_ = v___x_2314_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_size_2311_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2355_);
                        v___x_2357_ = v_reuseFailAlloc_2358_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2347_;
            }
            3 => {
                return v___x_2350_;
            }
            4 => {
                return v___x_2357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(
    mut v_lhs_2360_: *mut crate::leanh::LeanObject,
    mut v_rhs_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_a_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
    mut v_a_2366_: *mut crate::leanh::LeanObject,
    mut v_a_2367_: *mut crate::leanh::LeanObject,
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
    mut v_a_2370_: *mut crate::leanh::LeanObject,
    mut v_a_2371_: *mut crate::leanh::LeanObject,
    mut v_a_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2392_: u8 = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v_val_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v_fst_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut v_unused_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v_fst_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___y_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v_val_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2470_: u8 = 0;
    let mut v_fst_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2486_: u8 = 0;
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_unused_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2497_: u8 = 0;
    let mut v_binderType_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v_val_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v_fst_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_unused_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2542_: u8 = 0;
    let mut v_binderType_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v_val_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v_fst_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_unused_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2588_: u8 = 0;
    let mut v_type_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2608_: u8 = 0;
    let mut v_val_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v_fst_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_isSharedCheck_2629_: u8 = 0;
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_unused_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v_val_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v_fst_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_unused_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: u8 = 0;
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v_cache_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varTypes_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhss_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhss_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2712_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_isSharedCheck_2732_: u8 = 0;
    let mut v_a_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_a_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_a_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut v_a_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2760_: u8 = 0;
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2764_: u8 = 0;
    let mut v_a_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut v_a_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_a_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2423_ =
                    l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
                        v_a_2362_, v_a_2363_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2423_) == 0 {
                    v_a_2424_ = crate::leanh::lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2783_ = (!crate::leanh::lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v___x_2426_ = v___x_2423_;
                        v_isShared_2427_ = v_isSharedCheck_2783_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2424_);
                        crate::leanh::lean_dec(v___x_2423_);
                        v___x_2426_ = crate::leanh::lean_box(0);
                        v_isShared_2427_ = v_isSharedCheck_2783_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_2361_);
                    crate::leanh::lean_dec_ref(v_lhs_2360_);
                    v_a_2784_ = crate::leanh::lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2791_ = (!crate::leanh::lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2791_ == 0 {
                        v___x_2786_ = v___x_2423_;
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 68;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2784_);
                        crate::leanh::lean_dec(v___x_2423_);
                        v___x_2786_ = crate::leanh::lean_box(0);
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 68;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2392_ == 0 {
                    crate::leanh::lean_dec(v___y_2389_);
                    crate::leanh::lean_dec_ref(v___y_2388_);
                    crate::leanh::lean_dec_ref(v___y_2386_);
                    crate::leanh::lean_dec_ref(v___y_2382_);
                    crate::leanh::lean_dec(v___y_2376_);
                    v___x_2393_ = crate::leanh::lean_box(0);
                    v___x_2394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2394_, 0, v___x_2393_);
                    return v___x_2394_;
                } else {
                    v___x_2395_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_2382_, v___y_2388_, v___y_2379_, v___y_2386_, v___y_2390_, v___y_2387_, v___y_2383_, v___y_2391_, v___y_2381_, v___y_2377_, v___y_2384_, v___y_2385_, v___y_2378_, v___y_2380_);
                    if crate::leanh::lean_obj_tag(v___x_2395_) == 0 {
                        v_a_2396_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                        crate::leanh::lean_inc(v_a_2396_);
                        if crate::leanh::lean_obj_tag(v_a_2396_) == 0 {
                            crate::leanh::lean_dec(v___y_2389_);
                            crate::leanh::lean_dec(v___y_2376_);
                            return v___x_2395_;
                        } else {
                            v_isSharedCheck_2421_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2395_)) as u8;
                            if v_isSharedCheck_2421_ == 0 {
                                v_unused_2422_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                                crate::leanh::lean_dec(v_unused_2422_);
                                v___x_2398_ = v___x_2395_;
                                v_isShared_2399_ = v_isSharedCheck_2421_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2395_);
                                v___x_2398_ = crate::leanh::lean_box(0);
                                v_isShared_2399_ = v_isSharedCheck_2421_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2389_);
                        crate::leanh::lean_dec(v___y_2376_);
                        return v___x_2395_;
                    }
                }
            }
            2 => {
                v_val_2400_ = crate::leanh::lean_ctor_get(v_a_2396_, 0);
                v_isSharedCheck_2420_ = (!crate::leanh::lean_is_exclusive(v_a_2396_)) as u8;
                if v_isSharedCheck_2420_ == 0 {
                    v___x_2402_ = v_a_2396_;
                    v_isShared_2403_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2400_);
                    crate::leanh::lean_dec(v_a_2396_);
                    v___x_2402_ = crate::leanh::lean_box(0);
                    v_isShared_2403_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_2404_ = crate::leanh::lean_ctor_get(v_val_2400_, 0);
                v_snd_2405_ = crate::leanh::lean_ctor_get(v_val_2400_, 1);
                v_isSharedCheck_2419_ = (!crate::leanh::lean_is_exclusive(v_val_2400_)) as u8;
                if v_isSharedCheck_2419_ == 0 {
                    v___x_2407_ = v_val_2400_;
                    v_isShared_2408_ = v_isSharedCheck_2419_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2405_);
                    crate::leanh::lean_inc(v_fst_2404_);
                    crate::leanh::lean_dec(v_val_2400_);
                    v___x_2407_ = crate::leanh::lean_box(0);
                    v_isShared_2408_ = v_isSharedCheck_2419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2409_ = l_Lean_Expr_proj___override(v___y_2389_, v___y_2376_, v_fst_2404_);
                if v_isShared_2408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2407_, 0, v___x_2409_);
                    v___x_2411_ = v___x_2407_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_snd_2405_);
                    v___x_2411_ = v_reuseFailAlloc_2418_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2402_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2402_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2411_);
                    v___x_2413_ = v_reuseFailAlloc_2417_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2398_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
                    v___x_2415_ = v_reuseFailAlloc_2416_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2415_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_2424_) == 0 {
                    crate::leanh::lean_dec_ref(v_rhs_2361_);
                    crate::leanh::lean_dec_ref(v_lhs_2360_);
                    v___x_2428_ = crate::leanh::lean_box(0);
                    if v_isShared_2427_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2428_);
                        v___x_2430_ = v___x_2426_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                        v___x_2430_ = v_reuseFailAlloc_2431_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_val_2432_ = crate::leanh::lean_ctor_get(v_a_2424_, 0);
                    v_isSharedCheck_2782_ = (!crate::leanh::lean_is_exclusive(v_a_2424_)) as u8;
                    if v_isSharedCheck_2782_ == 0 {
                        v___x_2434_ = v_a_2424_;
                        v_isShared_2435_ = v_isSharedCheck_2782_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2432_);
                        crate::leanh::lean_dec(v_a_2424_);
                        v___x_2434_ = crate::leanh::lean_box(0);
                        v_isShared_2435_ = v_isSharedCheck_2782_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2430_;
            }
            10 => {
                v_fst_2436_ = crate::leanh::lean_ctor_get(v_val_2432_, 0);
                v_snd_2437_ = crate::leanh::lean_ctor_get(v_val_2432_, 1);
                v_isSharedCheck_2781_ = (!crate::leanh::lean_is_exclusive(v_val_2432_)) as u8;
                if v_isSharedCheck_2781_ == 0 {
                    v___x_2439_ = v_val_2432_;
                    v_isShared_2440_ = v_isSharedCheck_2781_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2437_);
                    crate::leanh::lean_inc(v_fst_2436_);
                    crate::leanh::lean_dec(v_val_2432_);
                    v___x_2439_ = crate::leanh::lean_box(0);
                    v_isShared_2440_ = v_isSharedCheck_2781_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2687_ = (crate::leanh::lean_unbox(v_fst_2436_) as u8);
                crate::leanh::lean_dec(v_fst_2436_);
                if v___x_2687_ == 0 {
                    crate::leanh::lean_del_object(v___x_2439_);
                    crate::leanh::lean_del_object(v___x_2434_);
                    v___y_2442_ = v_a_2362_;
                    v___y_2443_ = v_a_2364_;
                    v___y_2444_ = v_a_2365_;
                    v___y_2445_ = v_a_2366_;
                    v___y_2446_ = v_a_2367_;
                    v___y_2447_ = v_a_2368_;
                    v___y_2448_ = v_a_2369_;
                    v___y_2449_ = v_a_2370_;
                    v___y_2450_ = v_a_2371_;
                    v___y_2451_ = v_a_2372_;
                    v___y_2452_ = v_a_2373_;
                    state = 12;
                    continue;
                } else {
                    v___x_2688_ = l_Lean_Expr_hasLooseBVars(v_lhs_2360_);
                    if v___x_2688_ == 0 {
                        v___x_2689_ = l_Lean_Expr_hasLooseBVars(v_rhs_2361_);
                        if v___x_2689_ == 0 {
                            crate::leanh::lean_inc_ref(v_lhs_2360_);
                            v___x_2690_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_2360_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
                            if crate::leanh::lean_obj_tag(v___x_2690_) == 0 {
                                v_a_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                                crate::leanh::lean_inc(v_a_2691_);
                                crate::leanh::lean_dec_ref_known(v___x_2690_, 1);
                                crate::leanh::lean_inc_ref(v_rhs_2361_);
                                v___x_2692_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_2361_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
                                if crate::leanh::lean_obj_tag(v___x_2692_) == 0 {
                                    v_a_2693_ = crate::leanh::lean_ctor_get(v___x_2692_, 0);
                                    crate::leanh::lean_inc(v_a_2693_);
                                    crate::leanh::lean_dec_ref_known(v___x_2692_, 1);
                                    crate::leanh::lean_inc(v_a_2373_);
                                    crate::leanh::lean_inc_ref(v_a_2372_);
                                    crate::leanh::lean_inc(v_a_2371_);
                                    crate::leanh::lean_inc_ref(v_a_2370_);
                                    crate::leanh::lean_inc(v_a_2369_);
                                    crate::leanh::lean_inc_ref(v_a_2368_);
                                    crate::leanh::lean_inc(v_a_2367_);
                                    crate::leanh::lean_inc_ref(v_a_2366_);
                                    crate::leanh::lean_inc(v_a_2365_);
                                    crate::leanh::lean_inc(v_a_2364_);
                                    v___x_2694_ = lean_grind_process_new_facts(
                                        v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_,
                                        v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2694_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2694_, 1);
                                        v___x_2695_ = l_Lean_Meta_Grind_isEqv___redArg(
                                            v_a_2691_, v_a_2693_, v_a_2364_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2695_) == 0 {
                                            v_a_2696_ = crate::leanh::lean_ctor_get(v___x_2695_, 0);
                                            crate::leanh::lean_inc(v_a_2696_);
                                            crate::leanh::lean_dec_ref_known(v___x_2695_, 1);
                                            v___x_2697_ =
                                                (crate::leanh::lean_unbox(v_a_2696_) as u8);
                                            crate::leanh::lean_dec(v_a_2696_);
                                            if v___x_2697_ == 0 {
                                                crate::leanh::lean_dec(v_a_2693_);
                                                crate::leanh::lean_dec(v_a_2691_);
                                                crate::leanh::lean_del_object(v___x_2439_);
                                                crate::leanh::lean_del_object(v___x_2434_);
                                                v___y_2442_ = v_a_2362_;
                                                v___y_2443_ = v_a_2364_;
                                                v___y_2444_ = v_a_2365_;
                                                v___y_2445_ = v_a_2366_;
                                                v___y_2446_ = v_a_2367_;
                                                v___y_2447_ = v_a_2368_;
                                                v___y_2448_ = v_a_2369_;
                                                v___y_2449_ = v_a_2370_;
                                                v___y_2450_ = v_a_2371_;
                                                v___y_2451_ = v_a_2372_;
                                                v___y_2452_ = v_a_2373_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2693_);
                                                crate::leanh::lean_inc(v_a_2691_);
                                                v___x_2698_ = l_Lean_Meta_Grind_hasSameType(
                                                    v_a_2691_, v_a_2693_, v_a_2370_, v_a_2371_,
                                                    v_a_2372_, v_a_2373_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_2698_) == 0 {
                                                    v_a_2699_ =
                                                        crate::leanh::lean_ctor_get(v___x_2698_, 0);
                                                    crate::leanh::lean_inc(v_a_2699_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2698_,
                                                        1,
                                                    );
                                                    v___x_2700_ =
                                                        (crate::leanh::lean_unbox(v_a_2699_) as u8);
                                                    crate::leanh::lean_dec(v_a_2699_);
                                                    if v___x_2700_ == 0 {
                                                        crate::leanh::lean_dec(v_a_2693_);
                                                        crate::leanh::lean_dec(v_a_2691_);
                                                        crate::leanh::lean_del_object(v___x_2439_);
                                                        crate::leanh::lean_del_object(v___x_2434_);
                                                        v___y_2442_ = v_a_2362_;
                                                        v___y_2443_ = v_a_2364_;
                                                        v___y_2444_ = v_a_2365_;
                                                        v___y_2445_ = v_a_2366_;
                                                        v___y_2446_ = v_a_2367_;
                                                        v___y_2447_ = v_a_2368_;
                                                        v___y_2448_ = v_a_2369_;
                                                        v___y_2449_ = v_a_2370_;
                                                        v___y_2450_ = v_a_2371_;
                                                        v___y_2451_ = v_a_2372_;
                                                        v___y_2452_ = v_a_2373_;
                                                        state = 12;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_del_object(v___x_2426_);
                                                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                                                        crate::leanh::lean_dec_ref(v_lhs_2360_);
                                                        crate::leanh::lean_inc(v_a_2373_);
                                                        crate::leanh::lean_inc_ref(v_a_2372_);
                                                        crate::leanh::lean_inc(v_a_2371_);
                                                        crate::leanh::lean_inc_ref(v_a_2370_);
                                                        crate::leanh::lean_inc(v_a_2691_);
                                                        v___x_2701_ = lean_infer_type(
                                                            v_a_2691_, v_a_2370_, v_a_2371_,
                                                            v_a_2372_, v_a_2373_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_2701_)
                                                            == 0
                                                        {
                                                            v_a_2702_ = crate::leanh::lean_ctor_get(
                                                                v___x_2701_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2732_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2701_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2732_ == 0 {
                                                                v___x_2704_ = v___x_2701_;
                                                                v_isShared_2705_ =
                                                                    v_isSharedCheck_2732_;
                                                                state = 50;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2702_);
                                                                crate::leanh::lean_dec(v___x_2701_);
                                                                v___x_2704_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2705_ =
                                                                    v_isSharedCheck_2732_;
                                                                state = 50;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_a_2693_);
                                                            crate::leanh::lean_dec(v_a_2691_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2439_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_2437_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2434_,
                                                            );
                                                            v_a_2733_ = crate::leanh::lean_ctor_get(
                                                                v___x_2701_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2740_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2701_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2740_ == 0 {
                                                                v___x_2735_ = v___x_2701_;
                                                                v_isShared_2736_ =
                                                                    v_isSharedCheck_2740_;
                                                                state = 56;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2733_);
                                                                crate::leanh::lean_dec(v___x_2701_);
                                                                v___x_2735_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2736_ =
                                                                    v_isSharedCheck_2740_;
                                                                state = 56;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_2693_);
                                                    crate::leanh::lean_dec(v_a_2691_);
                                                    crate::leanh::lean_del_object(v___x_2439_);
                                                    crate::leanh::lean_dec(v_snd_2437_);
                                                    crate::leanh::lean_del_object(v___x_2434_);
                                                    crate::leanh::lean_del_object(v___x_2426_);
                                                    crate::leanh::lean_dec_ref(v_rhs_2361_);
                                                    crate::leanh::lean_dec_ref(v_lhs_2360_);
                                                    v_a_2741_ =
                                                        crate::leanh::lean_ctor_get(v___x_2698_, 0);
                                                    v_isSharedCheck_2748_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2698_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2748_ == 0 {
                                                        v___x_2743_ = v___x_2698_;
                                                        v_isShared_2744_ = v_isSharedCheck_2748_;
                                                        state = 58;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2741_);
                                                        crate::leanh::lean_dec(v___x_2698_);
                                                        v___x_2743_ = crate::leanh::lean_box(0);
                                                        v_isShared_2744_ = v_isSharedCheck_2748_;
                                                        state = 58;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_2693_);
                                            crate::leanh::lean_dec(v_a_2691_);
                                            crate::leanh::lean_del_object(v___x_2439_);
                                            crate::leanh::lean_dec(v_snd_2437_);
                                            crate::leanh::lean_del_object(v___x_2434_);
                                            crate::leanh::lean_del_object(v___x_2426_);
                                            crate::leanh::lean_dec_ref(v_rhs_2361_);
                                            crate::leanh::lean_dec_ref(v_lhs_2360_);
                                            v_a_2749_ = crate::leanh::lean_ctor_get(v___x_2695_, 0);
                                            v_isSharedCheck_2756_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2695_))
                                                    as u8;
                                            if v_isSharedCheck_2756_ == 0 {
                                                v___x_2751_ = v___x_2695_;
                                                v_isShared_2752_ = v_isSharedCheck_2756_;
                                                state = 60;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2749_);
                                                crate::leanh::lean_dec(v___x_2695_);
                                                v___x_2751_ = crate::leanh::lean_box(0);
                                                v_isShared_2752_ = v_isSharedCheck_2756_;
                                                state = 60;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2693_);
                                        crate::leanh::lean_dec(v_a_2691_);
                                        crate::leanh::lean_del_object(v___x_2439_);
                                        crate::leanh::lean_dec(v_snd_2437_);
                                        crate::leanh::lean_del_object(v___x_2434_);
                                        crate::leanh::lean_del_object(v___x_2426_);
                                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                                        crate::leanh::lean_dec_ref(v_lhs_2360_);
                                        v_a_2757_ = crate::leanh::lean_ctor_get(v___x_2694_, 0);
                                        v_isSharedCheck_2764_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2694_)) as u8;
                                        if v_isSharedCheck_2764_ == 0 {
                                            v___x_2759_ = v___x_2694_;
                                            v_isShared_2760_ = v_isSharedCheck_2764_;
                                            state = 62;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2757_);
                                            crate::leanh::lean_dec(v___x_2694_);
                                            v___x_2759_ = crate::leanh::lean_box(0);
                                            v_isShared_2760_ = v_isSharedCheck_2764_;
                                            state = 62;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2691_);
                                    crate::leanh::lean_del_object(v___x_2439_);
                                    crate::leanh::lean_dec(v_snd_2437_);
                                    crate::leanh::lean_del_object(v___x_2434_);
                                    crate::leanh::lean_del_object(v___x_2426_);
                                    crate::leanh::lean_dec_ref(v_rhs_2361_);
                                    crate::leanh::lean_dec_ref(v_lhs_2360_);
                                    v_a_2765_ = crate::leanh::lean_ctor_get(v___x_2692_, 0);
                                    v_isSharedCheck_2772_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2692_)) as u8;
                                    if v_isSharedCheck_2772_ == 0 {
                                        v___x_2767_ = v___x_2692_;
                                        v_isShared_2768_ = v_isSharedCheck_2772_;
                                        state = 64;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2765_);
                                        crate::leanh::lean_dec(v___x_2692_);
                                        v___x_2767_ = crate::leanh::lean_box(0);
                                        v_isShared_2768_ = v_isSharedCheck_2772_;
                                        state = 64;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2439_);
                                crate::leanh::lean_dec(v_snd_2437_);
                                crate::leanh::lean_del_object(v___x_2434_);
                                crate::leanh::lean_del_object(v___x_2426_);
                                crate::leanh::lean_dec_ref(v_rhs_2361_);
                                crate::leanh::lean_dec_ref(v_lhs_2360_);
                                v_a_2773_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                                v_isSharedCheck_2780_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2690_)) as u8;
                                if v_isSharedCheck_2780_ == 0 {
                                    v___x_2775_ = v___x_2690_;
                                    v_isShared_2776_ = v_isSharedCheck_2780_;
                                    state = 66;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2773_);
                                    crate::leanh::lean_dec(v___x_2690_);
                                    v___x_2775_ = crate::leanh::lean_box(0);
                                    v_isShared_2776_ = v_isSharedCheck_2780_;
                                    state = 66;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2439_);
                            crate::leanh::lean_del_object(v___x_2434_);
                            v___y_2442_ = v_a_2362_;
                            v___y_2443_ = v_a_2364_;
                            v___y_2444_ = v_a_2365_;
                            v___y_2445_ = v_a_2366_;
                            v___y_2446_ = v_a_2367_;
                            v___y_2447_ = v_a_2368_;
                            v___y_2448_ = v_a_2369_;
                            v___y_2449_ = v_a_2370_;
                            v___y_2450_ = v_a_2371_;
                            v___y_2451_ = v_a_2372_;
                            v___y_2452_ = v_a_2373_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2439_);
                        crate::leanh::lean_del_object(v___x_2434_);
                        v___y_2442_ = v_a_2362_;
                        v___y_2443_ = v_a_2364_;
                        v___y_2444_ = v_a_2365_;
                        v___y_2445_ = v_a_2366_;
                        v___y_2446_ = v_a_2367_;
                        v___y_2447_ = v_a_2368_;
                        v___y_2448_ = v_a_2369_;
                        v___y_2449_ = v_a_2370_;
                        v___y_2450_ = v_a_2371_;
                        v___y_2451_ = v_a_2372_;
                        v___y_2452_ = v_a_2373_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => match crate::leanh::lean_obj_tag(v_lhs_2360_) {
                5 => {
                    if crate::leanh::lean_obj_tag(v_rhs_2361_) == 5 {
                        crate::leanh::lean_del_object(v___x_2426_);
                        v_fn_2453_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 0);
                        crate::leanh::lean_inc_ref(v_fn_2453_);
                        v_arg_2454_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2454_);
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 2);
                        v_fn_2455_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 0);
                        crate::leanh::lean_inc_ref(v_fn_2455_);
                        v_arg_2456_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2456_);
                        crate::leanh::lean_dec_ref_known(v_rhs_2361_, 2);
                        v___x_2457_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_fn_2453_, v_fn_2455_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if crate::leanh::lean_obj_tag(v___x_2457_) == 0 {
                            v_a_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                            crate::leanh::lean_inc(v_a_2458_);
                            if crate::leanh::lean_obj_tag(v_a_2458_) == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2456_);
                                crate::leanh::lean_dec_ref(v_arg_2454_);
                                return v___x_2457_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2457_, 1);
                                v_val_2459_ = crate::leanh::lean_ctor_get(v_a_2458_, 0);
                                crate::leanh::lean_inc(v_val_2459_);
                                crate::leanh::lean_dec_ref_known(v_a_2458_, 1);
                                v_fst_2460_ = crate::leanh::lean_ctor_get(v_val_2459_, 0);
                                crate::leanh::lean_inc(v_fst_2460_);
                                v_snd_2461_ = crate::leanh::lean_ctor_get(v_val_2459_, 1);
                                crate::leanh::lean_inc(v_snd_2461_);
                                crate::leanh::lean_dec(v_val_2459_);
                                v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_arg_2454_, v_arg_2456_, v___y_2442_, v_snd_2461_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                if crate::leanh::lean_obj_tag(v___x_2462_) == 0 {
                                    v_a_2463_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                                    crate::leanh::lean_inc(v_a_2463_);
                                    if crate::leanh::lean_obj_tag(v_a_2463_) == 0 {
                                        crate::leanh::lean_dec(v_fst_2460_);
                                        return v___x_2462_;
                                    } else {
                                        v_isSharedCheck_2488_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2462_)) as u8;
                                        if v_isSharedCheck_2488_ == 0 {
                                            v_unused_2489_ =
                                                crate::leanh::lean_ctor_get(v___x_2462_, 0);
                                            crate::leanh::lean_dec(v_unused_2489_);
                                            v___x_2465_ = v___x_2462_;
                                            v_isShared_2466_ = v_isSharedCheck_2488_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2462_);
                                            v___x_2465_ = crate::leanh::lean_box(0);
                                            v_isShared_2466_ = v_isSharedCheck_2488_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_2460_);
                                    return v___x_2462_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_2456_);
                            crate::leanh::lean_dec_ref(v_arg_2454_);
                            return v___x_2457_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 2);
                        crate::leanh::lean_dec(v_snd_2437_);
                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                        v___x_2490_ = crate::leanh::lean_box(0);
                        if v_isShared_2427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2490_);
                            v___x_2492_ = v___x_2426_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_2493_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
                            v___x_2492_ = v_reuseFailAlloc_2493_;
                            state = 19;
                            continue;
                        }
                    }
                }
                6 => {
                    if crate::leanh::lean_obj_tag(v_rhs_2361_) == 6 {
                        crate::leanh::lean_del_object(v___x_2426_);
                        v_binderName_2494_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 0);
                        crate::leanh::lean_inc(v_binderName_2494_);
                        v_binderType_2495_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_2495_);
                        v_body_2496_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 2);
                        crate::leanh::lean_inc_ref(v_body_2496_);
                        v_binderInfo_2497_ = crate::leanh::lean_ctor_get_uint8(
                            v_lhs_2360_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 3);
                        v_binderType_2498_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_2498_);
                        v_body_2499_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 2);
                        crate::leanh::lean_inc_ref(v_body_2499_);
                        crate::leanh::lean_dec_ref_known(v_rhs_2361_, 3);
                        v___x_2500_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_2495_, v_binderType_2498_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if crate::leanh::lean_obj_tag(v___x_2500_) == 0 {
                            v_a_2501_ = crate::leanh::lean_ctor_get(v___x_2500_, 0);
                            crate::leanh::lean_inc(v_a_2501_);
                            if crate::leanh::lean_obj_tag(v_a_2501_) == 0 {
                                crate::leanh::lean_dec_ref(v_body_2499_);
                                crate::leanh::lean_dec_ref(v_body_2496_);
                                crate::leanh::lean_dec(v_binderName_2494_);
                                return v___x_2500_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2500_, 1);
                                v_val_2502_ = crate::leanh::lean_ctor_get(v_a_2501_, 0);
                                crate::leanh::lean_inc(v_val_2502_);
                                crate::leanh::lean_dec_ref_known(v_a_2501_, 1);
                                v_fst_2503_ = crate::leanh::lean_ctor_get(v_val_2502_, 0);
                                crate::leanh::lean_inc(v_fst_2503_);
                                v_snd_2504_ = crate::leanh::lean_ctor_get(v_val_2502_, 1);
                                crate::leanh::lean_inc(v_snd_2504_);
                                crate::leanh::lean_dec(v_val_2502_);
                                v___x_2505_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2506_ = lean_nat_add(v___y_2442_, v___x_2505_);
                                v___x_2507_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_2496_, v_body_2499_, v___x_2506_, v_snd_2504_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                crate::leanh::lean_dec(v___x_2506_);
                                if crate::leanh::lean_obj_tag(v___x_2507_) == 0 {
                                    v_a_2508_ = crate::leanh::lean_ctor_get(v___x_2507_, 0);
                                    crate::leanh::lean_inc(v_a_2508_);
                                    if crate::leanh::lean_obj_tag(v_a_2508_) == 0 {
                                        crate::leanh::lean_dec(v_fst_2503_);
                                        crate::leanh::lean_dec(v_binderName_2494_);
                                        return v___x_2507_;
                                    } else {
                                        v_isSharedCheck_2533_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2507_)) as u8;
                                        if v_isSharedCheck_2533_ == 0 {
                                            v_unused_2534_ =
                                                crate::leanh::lean_ctor_get(v___x_2507_, 0);
                                            crate::leanh::lean_dec(v_unused_2534_);
                                            v___x_2510_ = v___x_2507_;
                                            v_isShared_2511_ = v_isSharedCheck_2533_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2507_);
                                            v___x_2510_ = crate::leanh::lean_box(0);
                                            v_isShared_2511_ = v_isSharedCheck_2533_;
                                            state = 20;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_2503_);
                                    crate::leanh::lean_dec(v_binderName_2494_);
                                    return v___x_2507_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_2499_);
                            crate::leanh::lean_dec_ref(v_body_2496_);
                            crate::leanh::lean_dec(v_binderName_2494_);
                            return v___x_2500_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 3);
                        crate::leanh::lean_dec(v_snd_2437_);
                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                        v___x_2535_ = crate::leanh::lean_box(0);
                        if v_isShared_2427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2535_);
                            v___x_2537_ = v___x_2426_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_2538_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
                            v___x_2537_ = v_reuseFailAlloc_2538_;
                            state = 26;
                            continue;
                        }
                    }
                }
                7 => {
                    if crate::leanh::lean_obj_tag(v_rhs_2361_) == 7 {
                        crate::leanh::lean_del_object(v___x_2426_);
                        v_binderName_2539_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 0);
                        crate::leanh::lean_inc(v_binderName_2539_);
                        v_binderType_2540_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_2540_);
                        v_body_2541_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 2);
                        crate::leanh::lean_inc_ref(v_body_2541_);
                        v_binderInfo_2542_ = crate::leanh::lean_ctor_get_uint8(
                            v_lhs_2360_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 3);
                        v_binderType_2543_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_2543_);
                        v_body_2544_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 2);
                        crate::leanh::lean_inc_ref(v_body_2544_);
                        crate::leanh::lean_dec_ref_known(v_rhs_2361_, 3);
                        v___x_2545_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_2540_, v_binderType_2543_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if crate::leanh::lean_obj_tag(v___x_2545_) == 0 {
                            v_a_2546_ = crate::leanh::lean_ctor_get(v___x_2545_, 0);
                            crate::leanh::lean_inc(v_a_2546_);
                            if crate::leanh::lean_obj_tag(v_a_2546_) == 0 {
                                crate::leanh::lean_dec_ref(v_body_2544_);
                                crate::leanh::lean_dec_ref(v_body_2541_);
                                crate::leanh::lean_dec(v_binderName_2539_);
                                return v___x_2545_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2545_, 1);
                                v_val_2547_ = crate::leanh::lean_ctor_get(v_a_2546_, 0);
                                crate::leanh::lean_inc(v_val_2547_);
                                crate::leanh::lean_dec_ref_known(v_a_2546_, 1);
                                v_fst_2548_ = crate::leanh::lean_ctor_get(v_val_2547_, 0);
                                crate::leanh::lean_inc(v_fst_2548_);
                                v_snd_2549_ = crate::leanh::lean_ctor_get(v_val_2547_, 1);
                                crate::leanh::lean_inc(v_snd_2549_);
                                crate::leanh::lean_dec(v_val_2547_);
                                v___x_2550_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2551_ = lean_nat_add(v___y_2442_, v___x_2550_);
                                v___x_2552_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_2541_, v_body_2544_, v___x_2551_, v_snd_2549_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                crate::leanh::lean_dec(v___x_2551_);
                                if crate::leanh::lean_obj_tag(v___x_2552_) == 0 {
                                    v_a_2553_ = crate::leanh::lean_ctor_get(v___x_2552_, 0);
                                    crate::leanh::lean_inc(v_a_2553_);
                                    if crate::leanh::lean_obj_tag(v_a_2553_) == 0 {
                                        crate::leanh::lean_dec(v_fst_2548_);
                                        crate::leanh::lean_dec(v_binderName_2539_);
                                        return v___x_2552_;
                                    } else {
                                        v_isSharedCheck_2578_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2552_)) as u8;
                                        if v_isSharedCheck_2578_ == 0 {
                                            v_unused_2579_ =
                                                crate::leanh::lean_ctor_get(v___x_2552_, 0);
                                            crate::leanh::lean_dec(v_unused_2579_);
                                            v___x_2555_ = v___x_2552_;
                                            v_isShared_2556_ = v_isSharedCheck_2578_;
                                            state = 27;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2552_);
                                            v___x_2555_ = crate::leanh::lean_box(0);
                                            v_isShared_2556_ = v_isSharedCheck_2578_;
                                            state = 27;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_2548_);
                                    crate::leanh::lean_dec(v_binderName_2539_);
                                    return v___x_2552_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_2544_);
                            crate::leanh::lean_dec_ref(v_body_2541_);
                            crate::leanh::lean_dec(v_binderName_2539_);
                            return v___x_2545_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 3);
                        crate::leanh::lean_dec(v_snd_2437_);
                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                        v___x_2580_ = crate::leanh::lean_box(0);
                        if v_isShared_2427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2580_);
                            v___x_2582_ = v___x_2426_;
                            state = 33;
                            continue;
                        } else {
                            v_reuseFailAlloc_2583_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
                            v___x_2582_ = v_reuseFailAlloc_2583_;
                            state = 33;
                            continue;
                        }
                    }
                }
                8 => {
                    if crate::leanh::lean_obj_tag(v_rhs_2361_) == 8 {
                        crate::leanh::lean_del_object(v___x_2426_);
                        v_declName_2584_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 0);
                        crate::leanh::lean_inc(v_declName_2584_);
                        v_type_2585_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 1);
                        crate::leanh::lean_inc_ref(v_type_2585_);
                        v_value_2586_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 2);
                        crate::leanh::lean_inc_ref(v_value_2586_);
                        v_body_2587_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 3);
                        crate::leanh::lean_inc_ref(v_body_2587_);
                        v_nondep_2588_ = crate::leanh::lean_ctor_get_uint8(
                            v_lhs_2360_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 4);
                        v_type_2589_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 1);
                        crate::leanh::lean_inc_ref(v_type_2589_);
                        v_value_2590_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 2);
                        crate::leanh::lean_inc_ref(v_value_2590_);
                        v_body_2591_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 3);
                        crate::leanh::lean_inc_ref(v_body_2591_);
                        crate::leanh::lean_dec_ref_known(v_rhs_2361_, 4);
                        v___x_2592_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_type_2585_, v_type_2589_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if crate::leanh::lean_obj_tag(v___x_2592_) == 0 {
                            v_a_2593_ = crate::leanh::lean_ctor_get(v___x_2592_, 0);
                            crate::leanh::lean_inc(v_a_2593_);
                            if crate::leanh::lean_obj_tag(v_a_2593_) == 0 {
                                crate::leanh::lean_dec_ref(v_body_2591_);
                                crate::leanh::lean_dec_ref(v_value_2590_);
                                crate::leanh::lean_dec_ref(v_body_2587_);
                                crate::leanh::lean_dec_ref(v_value_2586_);
                                crate::leanh::lean_dec(v_declName_2584_);
                                return v___x_2592_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2592_, 1);
                                v_val_2594_ = crate::leanh::lean_ctor_get(v_a_2593_, 0);
                                crate::leanh::lean_inc(v_val_2594_);
                                crate::leanh::lean_dec_ref_known(v_a_2593_, 1);
                                v_fst_2595_ = crate::leanh::lean_ctor_get(v_val_2594_, 0);
                                crate::leanh::lean_inc(v_fst_2595_);
                                v_snd_2596_ = crate::leanh::lean_ctor_get(v_val_2594_, 1);
                                crate::leanh::lean_inc(v_snd_2596_);
                                crate::leanh::lean_dec(v_val_2594_);
                                v___x_2597_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_value_2586_, v_value_2590_, v___y_2442_, v_snd_2596_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                if crate::leanh::lean_obj_tag(v___x_2597_) == 0 {
                                    v_a_2598_ = crate::leanh::lean_ctor_get(v___x_2597_, 0);
                                    crate::leanh::lean_inc(v_a_2598_);
                                    if crate::leanh::lean_obj_tag(v_a_2598_) == 0 {
                                        crate::leanh::lean_dec(v_fst_2595_);
                                        crate::leanh::lean_dec_ref(v_body_2591_);
                                        crate::leanh::lean_dec_ref(v_body_2587_);
                                        crate::leanh::lean_dec(v_declName_2584_);
                                        return v___x_2597_;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_2597_, 1);
                                        v_val_2599_ = crate::leanh::lean_ctor_get(v_a_2598_, 0);
                                        crate::leanh::lean_inc(v_val_2599_);
                                        crate::leanh::lean_dec_ref_known(v_a_2598_, 1);
                                        v_fst_2600_ = crate::leanh::lean_ctor_get(v_val_2599_, 0);
                                        crate::leanh::lean_inc(v_fst_2600_);
                                        v_snd_2601_ = crate::leanh::lean_ctor_get(v_val_2599_, 1);
                                        crate::leanh::lean_inc(v_snd_2601_);
                                        crate::leanh::lean_dec(v_val_2599_);
                                        v___x_2602_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_2603_ = lean_nat_add(v___y_2442_, v___x_2602_);
                                        v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_2587_, v_body_2591_, v___x_2603_, v_snd_2601_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                        crate::leanh::lean_dec(v___x_2603_);
                                        if crate::leanh::lean_obj_tag(v___x_2604_) == 0 {
                                            v_a_2605_ = crate::leanh::lean_ctor_get(v___x_2604_, 0);
                                            crate::leanh::lean_inc(v_a_2605_);
                                            if crate::leanh::lean_obj_tag(v_a_2605_) == 0 {
                                                crate::leanh::lean_dec(v_fst_2600_);
                                                crate::leanh::lean_dec(v_fst_2595_);
                                                crate::leanh::lean_dec(v_declName_2584_);
                                                return v___x_2604_;
                                            } else {
                                                v_isSharedCheck_2630_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2604_))
                                                        as u8;
                                                if v_isSharedCheck_2630_ == 0 {
                                                    v_unused_2631_ =
                                                        crate::leanh::lean_ctor_get(v___x_2604_, 0);
                                                    crate::leanh::lean_dec(v_unused_2631_);
                                                    v___x_2607_ = v___x_2604_;
                                                    v_isShared_2608_ = v_isSharedCheck_2630_;
                                                    state = 34;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2604_);
                                                    v___x_2607_ = crate::leanh::lean_box(0);
                                                    v_isShared_2608_ = v_isSharedCheck_2630_;
                                                    state = 34;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_fst_2600_);
                                            crate::leanh::lean_dec(v_fst_2595_);
                                            crate::leanh::lean_dec(v_declName_2584_);
                                            return v___x_2604_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_2595_);
                                    crate::leanh::lean_dec_ref(v_body_2591_);
                                    crate::leanh::lean_dec_ref(v_body_2587_);
                                    crate::leanh::lean_dec(v_declName_2584_);
                                    return v___x_2597_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_2591_);
                            crate::leanh::lean_dec_ref(v_value_2590_);
                            crate::leanh::lean_dec_ref(v_body_2587_);
                            crate::leanh::lean_dec_ref(v_value_2586_);
                            crate::leanh::lean_dec(v_declName_2584_);
                            return v___x_2592_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 4);
                        crate::leanh::lean_dec(v_snd_2437_);
                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                        v___x_2632_ = crate::leanh::lean_box(0);
                        if v_isShared_2427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2632_);
                            v___x_2634_ = v___x_2426_;
                            state = 40;
                            continue;
                        } else {
                            v_reuseFailAlloc_2635_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
                            v___x_2634_ = v_reuseFailAlloc_2635_;
                            state = 40;
                            continue;
                        }
                    }
                }
                10 => {
                    if crate::leanh::lean_obj_tag(v_rhs_2361_) == 10 {
                        crate::leanh::lean_del_object(v___x_2426_);
                        v_data_2636_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 0);
                        crate::leanh::lean_inc(v_data_2636_);
                        v_expr_2637_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 1);
                        crate::leanh::lean_inc_ref(v_expr_2637_);
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 2);
                        v_expr_2638_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 1);
                        crate::leanh::lean_inc_ref(v_expr_2638_);
                        crate::leanh::lean_dec_ref_known(v_rhs_2361_, 2);
                        v___x_2639_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_expr_2637_, v_expr_2638_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if crate::leanh::lean_obj_tag(v___x_2639_) == 0 {
                            v_a_2640_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                            crate::leanh::lean_inc(v_a_2640_);
                            if crate::leanh::lean_obj_tag(v_a_2640_) == 0 {
                                crate::leanh::lean_dec(v_data_2636_);
                                return v___x_2639_;
                            } else {
                                v_isSharedCheck_2665_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2639_)) as u8;
                                if v_isSharedCheck_2665_ == 0 {
                                    v_unused_2666_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                                    crate::leanh::lean_dec(v_unused_2666_);
                                    v___x_2642_ = v___x_2639_;
                                    v_isShared_2643_ = v_isSharedCheck_2665_;
                                    state = 41;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2639_);
                                    v___x_2642_ = crate::leanh::lean_box(0);
                                    v_isShared_2643_ = v_isSharedCheck_2665_;
                                    state = 41;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_data_2636_);
                            return v___x_2639_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 2);
                        crate::leanh::lean_dec(v_snd_2437_);
                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                        v___x_2667_ = crate::leanh::lean_box(0);
                        if v_isShared_2427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2667_);
                            v___x_2669_ = v___x_2426_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2670_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
                            v___x_2669_ = v_reuseFailAlloc_2670_;
                            state = 47;
                            continue;
                        }
                    }
                }
                11 => {
                    if crate::leanh::lean_obj_tag(v_rhs_2361_) == 11 {
                        crate::leanh::lean_del_object(v___x_2426_);
                        v_typeName_2671_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 0);
                        crate::leanh::lean_inc(v_typeName_2671_);
                        v_idx_2672_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 1);
                        crate::leanh::lean_inc(v_idx_2672_);
                        v_struct_2673_ = crate::leanh::lean_ctor_get(v_lhs_2360_, 2);
                        crate::leanh::lean_inc_ref(v_struct_2673_);
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 3);
                        v_typeName_2674_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 0);
                        crate::leanh::lean_inc(v_typeName_2674_);
                        v_idx_2675_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 1);
                        crate::leanh::lean_inc(v_idx_2675_);
                        v_struct_2676_ = crate::leanh::lean_ctor_get(v_rhs_2361_, 2);
                        crate::leanh::lean_inc_ref(v_struct_2676_);
                        crate::leanh::lean_dec_ref_known(v_rhs_2361_, 3);
                        v___x_2677_ = lean_name_eq(v_typeName_2671_, v_typeName_2674_);
                        crate::leanh::lean_dec(v_typeName_2674_);
                        if v___x_2677_ == 0 {
                            crate::leanh::lean_dec(v_idx_2675_);
                            v___y_2376_ = v_idx_2672_;
                            v___y_2377_ = v___y_2448_;
                            v___y_2378_ = v___y_2451_;
                            v___y_2379_ = v___y_2442_;
                            v___y_2380_ = v___y_2452_;
                            v___y_2381_ = v___y_2447_;
                            v___y_2382_ = v_struct_2673_;
                            v___y_2383_ = v___y_2445_;
                            v___y_2384_ = v___y_2449_;
                            v___y_2385_ = v___y_2450_;
                            v___y_2386_ = v_snd_2437_;
                            v___y_2387_ = v___y_2444_;
                            v___y_2388_ = v_struct_2676_;
                            v___y_2389_ = v_typeName_2671_;
                            v___y_2390_ = v___y_2443_;
                            v___y_2391_ = v___y_2446_;
                            v___y_2392_ = v___x_2677_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2678_ = lean_nat_dec_eq(v_idx_2672_, v_idx_2675_);
                            crate::leanh::lean_dec(v_idx_2675_);
                            v___y_2376_ = v_idx_2672_;
                            v___y_2377_ = v___y_2448_;
                            v___y_2378_ = v___y_2451_;
                            v___y_2379_ = v___y_2442_;
                            v___y_2380_ = v___y_2452_;
                            v___y_2381_ = v___y_2447_;
                            v___y_2382_ = v_struct_2673_;
                            v___y_2383_ = v___y_2445_;
                            v___y_2384_ = v___y_2449_;
                            v___y_2385_ = v___y_2450_;
                            v___y_2386_ = v_snd_2437_;
                            v___y_2387_ = v___y_2444_;
                            v___y_2388_ = v_struct_2676_;
                            v___y_2389_ = v_typeName_2671_;
                            v___y_2390_ = v___y_2443_;
                            v___y_2391_ = v___y_2446_;
                            v___y_2392_ = v___x_2678_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_lhs_2360_, 3);
                        crate::leanh::lean_dec(v_snd_2437_);
                        crate::leanh::lean_dec_ref(v_rhs_2361_);
                        v___x_2679_ = crate::leanh::lean_box(0);
                        if v_isShared_2427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2679_);
                            v___x_2681_ = v___x_2426_;
                            state = 48;
                            continue;
                        } else {
                            v_reuseFailAlloc_2682_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
                            v___x_2681_ = v_reuseFailAlloc_2682_;
                            state = 48;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_snd_2437_);
                    crate::leanh::lean_dec_ref(v_rhs_2361_);
                    crate::leanh::lean_dec_ref(v_lhs_2360_);
                    v___x_2683_ = crate::leanh::lean_box(0);
                    if v_isShared_2427_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2683_);
                        v___x_2685_ = v___x_2426_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_2686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
                        v___x_2685_ = v_reuseFailAlloc_2686_;
                        state = 49;
                        continue;
                    }
                }
            },
            13 => {
                v_val_2467_ = crate::leanh::lean_ctor_get(v_a_2463_, 0);
                v_isSharedCheck_2487_ = (!crate::leanh::lean_is_exclusive(v_a_2463_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v___x_2469_ = v_a_2463_;
                    v_isShared_2470_ = v_isSharedCheck_2487_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2467_);
                    crate::leanh::lean_dec(v_a_2463_);
                    v___x_2469_ = crate::leanh::lean_box(0);
                    v_isShared_2470_ = v_isSharedCheck_2487_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_fst_2471_ = crate::leanh::lean_ctor_get(v_val_2467_, 0);
                v_snd_2472_ = crate::leanh::lean_ctor_get(v_val_2467_, 1);
                v_isSharedCheck_2486_ = (!crate::leanh::lean_is_exclusive(v_val_2467_)) as u8;
                if v_isSharedCheck_2486_ == 0 {
                    v___x_2474_ = v_val_2467_;
                    v_isShared_2475_ = v_isSharedCheck_2486_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2472_);
                    crate::leanh::lean_inc(v_fst_2471_);
                    crate::leanh::lean_dec(v_val_2467_);
                    v___x_2474_ = crate::leanh::lean_box(0);
                    v_isShared_2475_ = v_isSharedCheck_2486_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2476_ = l_Lean_Expr_app___override(v_fst_2460_, v_fst_2471_);
                if v_isShared_2475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2474_, 0, v___x_2476_);
                    v___x_2478_ = v___x_2474_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_snd_2472_);
                    v___x_2478_ = v_reuseFailAlloc_2485_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2469_, 0, v___x_2478_);
                    v___x_2480_ = v___x_2469_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2478_);
                    v___x_2480_ = v_reuseFailAlloc_2484_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2465_, 0, v___x_2480_);
                    v___x_2482_ = v___x_2465_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2482_;
            }
            19 => {
                return v___x_2492_;
            }
            20 => {
                v_val_2512_ = crate::leanh::lean_ctor_get(v_a_2508_, 0);
                v_isSharedCheck_2532_ = (!crate::leanh::lean_is_exclusive(v_a_2508_)) as u8;
                if v_isSharedCheck_2532_ == 0 {
                    v___x_2514_ = v_a_2508_;
                    v_isShared_2515_ = v_isSharedCheck_2532_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2512_);
                    crate::leanh::lean_dec(v_a_2508_);
                    v___x_2514_ = crate::leanh::lean_box(0);
                    v_isShared_2515_ = v_isSharedCheck_2532_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v_fst_2516_ = crate::leanh::lean_ctor_get(v_val_2512_, 0);
                v_snd_2517_ = crate::leanh::lean_ctor_get(v_val_2512_, 1);
                v_isSharedCheck_2531_ = (!crate::leanh::lean_is_exclusive(v_val_2512_)) as u8;
                if v_isSharedCheck_2531_ == 0 {
                    v___x_2519_ = v_val_2512_;
                    v_isShared_2520_ = v_isSharedCheck_2531_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2517_);
                    crate::leanh::lean_inc(v_fst_2516_);
                    crate::leanh::lean_dec(v_val_2512_);
                    v___x_2519_ = crate::leanh::lean_box(0);
                    v_isShared_2520_ = v_isSharedCheck_2531_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_2521_ = l_Lean_mkLambda(
                    v_binderName_2494_,
                    v_binderInfo_2497_,
                    v_fst_2503_,
                    v_fst_2516_,
                );
                if v_isShared_2520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2521_);
                    v___x_2523_ = v___x_2519_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_snd_2517_);
                    v___x_2523_ = v_reuseFailAlloc_2530_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2523_);
                    v___x_2525_ = v___x_2514_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2523_);
                    v___x_2525_ = v_reuseFailAlloc_2529_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_2511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2525_);
                    v___x_2527_ = v___x_2510_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2527_;
            }
            26 => {
                return v___x_2537_;
            }
            27 => {
                v_val_2557_ = crate::leanh::lean_ctor_get(v_a_2553_, 0);
                v_isSharedCheck_2577_ = (!crate::leanh::lean_is_exclusive(v_a_2553_)) as u8;
                if v_isSharedCheck_2577_ == 0 {
                    v___x_2559_ = v_a_2553_;
                    v_isShared_2560_ = v_isSharedCheck_2577_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2557_);
                    crate::leanh::lean_dec(v_a_2553_);
                    v___x_2559_ = crate::leanh::lean_box(0);
                    v_isShared_2560_ = v_isSharedCheck_2577_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v_fst_2561_ = crate::leanh::lean_ctor_get(v_val_2557_, 0);
                v_snd_2562_ = crate::leanh::lean_ctor_get(v_val_2557_, 1);
                v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v_val_2557_)) as u8;
                if v_isSharedCheck_2576_ == 0 {
                    v___x_2564_ = v_val_2557_;
                    v_isShared_2565_ = v_isSharedCheck_2576_;
                    state = 29;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2562_);
                    crate::leanh::lean_inc(v_fst_2561_);
                    crate::leanh::lean_dec(v_val_2557_);
                    v___x_2564_ = crate::leanh::lean_box(0);
                    v_isShared_2565_ = v_isSharedCheck_2576_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_2566_ = l_Lean_mkForall(
                    v_binderName_2539_,
                    v_binderInfo_2542_,
                    v_fst_2548_,
                    v_fst_2561_,
                );
                if v_isShared_2565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2564_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_snd_2562_);
                    v___x_2568_ = v_reuseFailAlloc_2575_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_2560_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2559_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2559_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2574_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_2556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2570_);
                    v___x_2572_ = v___x_2555_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
                    v___x_2572_ = v_reuseFailAlloc_2573_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2572_;
            }
            33 => {
                return v___x_2582_;
            }
            34 => {
                v_val_2609_ = crate::leanh::lean_ctor_get(v_a_2605_, 0);
                v_isSharedCheck_2629_ = (!crate::leanh::lean_is_exclusive(v_a_2605_)) as u8;
                if v_isSharedCheck_2629_ == 0 {
                    v___x_2611_ = v_a_2605_;
                    v_isShared_2612_ = v_isSharedCheck_2629_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2609_);
                    crate::leanh::lean_dec(v_a_2605_);
                    v___x_2611_ = crate::leanh::lean_box(0);
                    v_isShared_2612_ = v_isSharedCheck_2629_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v_fst_2613_ = crate::leanh::lean_ctor_get(v_val_2609_, 0);
                v_snd_2614_ = crate::leanh::lean_ctor_get(v_val_2609_, 1);
                v_isSharedCheck_2628_ = (!crate::leanh::lean_is_exclusive(v_val_2609_)) as u8;
                if v_isSharedCheck_2628_ == 0 {
                    v___x_2616_ = v_val_2609_;
                    v_isShared_2617_ = v_isSharedCheck_2628_;
                    state = 36;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2614_);
                    crate::leanh::lean_inc(v_fst_2613_);
                    crate::leanh::lean_dec(v_val_2609_);
                    v___x_2616_ = crate::leanh::lean_box(0);
                    v_isShared_2617_ = v_isSharedCheck_2628_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_2618_ = l_Lean_Expr_letE___override(
                    v_declName_2584_,
                    v_fst_2595_,
                    v_fst_2600_,
                    v_fst_2613_,
                    v_nondep_2588_,
                );
                if v_isShared_2617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2616_, 0, v___x_2618_);
                    v___x_2620_ = v___x_2616_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_snd_2614_);
                    v___x_2620_ = v_reuseFailAlloc_2627_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2612_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2611_, 0, v___x_2620_);
                    v___x_2622_ = v___x_2611_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2620_);
                    v___x_2622_ = v_reuseFailAlloc_2626_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_2608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2607_, 0, v___x_2622_);
                    v___x_2624_ = v___x_2607_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
                    v___x_2624_ = v_reuseFailAlloc_2625_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2624_;
            }
            40 => {
                return v___x_2634_;
            }
            41 => {
                v_val_2644_ = crate::leanh::lean_ctor_get(v_a_2640_, 0);
                v_isSharedCheck_2664_ = (!crate::leanh::lean_is_exclusive(v_a_2640_)) as u8;
                if v_isSharedCheck_2664_ == 0 {
                    v___x_2646_ = v_a_2640_;
                    v_isShared_2647_ = v_isSharedCheck_2664_;
                    state = 42;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2644_);
                    crate::leanh::lean_dec(v_a_2640_);
                    v___x_2646_ = crate::leanh::lean_box(0);
                    v_isShared_2647_ = v_isSharedCheck_2664_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v_fst_2648_ = crate::leanh::lean_ctor_get(v_val_2644_, 0);
                v_snd_2649_ = crate::leanh::lean_ctor_get(v_val_2644_, 1);
                v_isSharedCheck_2663_ = (!crate::leanh::lean_is_exclusive(v_val_2644_)) as u8;
                if v_isSharedCheck_2663_ == 0 {
                    v___x_2651_ = v_val_2644_;
                    v_isShared_2652_ = v_isSharedCheck_2663_;
                    state = 43;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2649_);
                    crate::leanh::lean_inc(v_fst_2648_);
                    crate::leanh::lean_dec(v_val_2644_);
                    v___x_2651_ = crate::leanh::lean_box(0);
                    v_isShared_2652_ = v_isSharedCheck_2663_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_2653_ = l_Lean_Expr_mdata___override(v_data_2636_, v_fst_2648_);
                if v_isShared_2652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2651_, 0, v___x_2653_);
                    v___x_2655_ = v___x_2651_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_snd_2649_);
                    v___x_2655_ = v_reuseFailAlloc_2662_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2655_);
                    v___x_2657_ = v___x_2646_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2655_);
                    v___x_2657_ = v_reuseFailAlloc_2661_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_2643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2642_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2659_;
            }
            47 => {
                return v___x_2669_;
            }
            48 => {
                return v___x_2681_;
            }
            49 => {
                return v___x_2685_;
            }
            50 => {
                v_cache_2706_ = crate::leanh::lean_ctor_get(v_snd_2437_, 0);
                v_varTypes_2707_ = crate::leanh::lean_ctor_get(v_snd_2437_, 1);
                v_lhss_2708_ = crate::leanh::lean_ctor_get(v_snd_2437_, 2);
                v_rhss_2709_ = crate::leanh::lean_ctor_get(v_snd_2437_, 3);
                v_isSharedCheck_2731_ = (!crate::leanh::lean_is_exclusive(v_snd_2437_)) as u8;
                if v_isSharedCheck_2731_ == 0 {
                    v___x_2711_ = v_snd_2437_;
                    v_isShared_2712_ = v_isSharedCheck_2731_;
                    state = 51;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhss_2709_);
                    crate::leanh::lean_inc(v_lhss_2708_);
                    crate::leanh::lean_inc(v_varTypes_2707_);
                    crate::leanh::lean_inc(v_cache_2706_);
                    crate::leanh::lean_dec(v_snd_2437_);
                    v___x_2711_ = crate::leanh::lean_box(0);
                    v_isShared_2712_ = v_isSharedCheck_2731_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___x_2713_ = lean_array_get_size(v_varTypes_2707_);
                v___x_2714_ = lean_nat_add(v___x_2713_, v_a_2362_);
                v___x_2715_ = lean_array_push(v_varTypes_2707_, v_a_2702_);
                v___x_2716_ = lean_array_push(v_lhss_2708_, v_a_2691_);
                v___x_2717_ = lean_array_push(v_rhss_2709_, v_a_2693_);
                if v_isShared_2712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2711_, 3, v___x_2717_);
                    crate::leanh::lean_ctor_set(v___x_2711_, 2, v___x_2716_);
                    crate::leanh::lean_ctor_set(v___x_2711_, 1, v___x_2715_);
                    v___x_2719_ = v___x_2711_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_cache_2706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 2, v___x_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 3, v___x_2717_);
                    v___x_2719_ = v_reuseFailAlloc_2730_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_2720_ = l_Lean_mkBVar(v___x_2714_);
                if v_isShared_2440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2439_, 1, v___x_2719_);
                    crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2720_);
                    v___x_2722_ = v___x_2439_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2719_);
                    v___x_2722_ = v_reuseFailAlloc_2729_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_2435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2434_, 0, v___x_2722_);
                    v___x_2724_ = v___x_2434_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2722_);
                    v___x_2724_ = v_reuseFailAlloc_2728_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                if v_isShared_2705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2724_);
                    v___x_2726_ = v___x_2704_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_2726_;
            }
            56 => {
                if v_isShared_2736_ == 0 {
                    v___x_2738_ = v___x_2735_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_2739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
                    v___x_2738_ = v_reuseFailAlloc_2739_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_2738_;
            }
            58 => {
                if v_isShared_2744_ == 0 {
                    v___x_2746_ = v___x_2743_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
                    v___x_2746_ = v_reuseFailAlloc_2747_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_2746_;
            }
            60 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_2754_;
            }
            62 => {
                if v_isShared_2760_ == 0 {
                    v___x_2762_ = v___x_2759_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
                    v___x_2762_ = v_reuseFailAlloc_2763_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_2762_;
            }
            64 => {
                if v_isShared_2768_ == 0 {
                    v___x_2770_ = v___x_2767_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
                    v___x_2770_ = v_reuseFailAlloc_2771_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2770_;
            }
            66 => {
                if v_isShared_2776_ == 0 {
                    v___x_2778_ = v___x_2775_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2779_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
                    v___x_2778_ = v_reuseFailAlloc_2779_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2778_;
            }
            68 => {
                if v_isShared_2787_ == 0 {
                    v___x_2789_ = v___x_2786_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_2789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(
    mut v_lhs_2792_: *mut crate::leanh::LeanObject,
    mut v_rhs_2793_: *mut crate::leanh::LeanObject,
    mut v_a_2794_: *mut crate::leanh::LeanObject,
    mut v_a_2795_: *mut crate::leanh::LeanObject,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
    mut v_a_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2807_: u8 = 0;
    let mut v_cache_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v_val_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v_snd_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v_cache_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varTypes_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhss_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhss_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2841_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2855_: u8 = 0;
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_isSharedCheck_2858_: u8 = 0;
    let mut v_unused_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2807_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_lhs_2792_,
                        v_rhs_2793_,
                    );
                if v___x_2807_ == 0 {
                    v_cache_2808_ = crate::leanh::lean_ctor_get(v_a_2795_, 0);
                    crate::leanh::lean_inc_ref(v_rhs_2793_);
                    crate::leanh::lean_inc_ref(v_lhs_2792_);
                    v___x_2809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2809_, 0, v_lhs_2792_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 1, v_rhs_2793_);
                    v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_2808_, v___x_2809_);
                    if crate::leanh::lean_obj_tag(v___x_2810_) == 1 {
                        crate::leanh::lean_dec_ref_known(v___x_2809_, 2);
                        crate::leanh::lean_dec_ref(v_rhs_2793_);
                        crate::leanh::lean_dec_ref(v_lhs_2792_);
                        v_val_2811_ = crate::leanh::lean_ctor_get(v___x_2810_, 0);
                        v_isSharedCheck_2820_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2810_)) as u8;
                        if v_isSharedCheck_2820_ == 0 {
                            v___x_2813_ = v___x_2810_;
                            v_isShared_2814_ = v_isSharedCheck_2820_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2811_);
                            crate::leanh::lean_dec(v___x_2810_);
                            v___x_2813_ = crate::leanh::lean_box(0);
                            v_isShared_2814_ = v_isSharedCheck_2820_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2810_);
                        v___x_2821_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_2792_, v_rhs_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
                        if crate::leanh::lean_obj_tag(v___x_2821_) == 0 {
                            v_a_2822_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                            crate::leanh::lean_inc(v_a_2822_);
                            if crate::leanh::lean_obj_tag(v_a_2822_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2809_, 2);
                                return v___x_2821_;
                            } else {
                                v_isSharedCheck_2858_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2821_)) as u8;
                                if v_isSharedCheck_2858_ == 0 {
                                    v_unused_2859_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                                    crate::leanh::lean_dec(v_unused_2859_);
                                    v___x_2824_ = v___x_2821_;
                                    v_isShared_2825_ = v_isSharedCheck_2858_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2821_);
                                    v___x_2824_ = crate::leanh::lean_box(0);
                                    v_isShared_2825_ = v_isSharedCheck_2858_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2809_, 2);
                            return v___x_2821_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_2793_);
                    v___x_2860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2860_, 0, v_lhs_2792_);
                    crate::leanh::lean_ctor_set(v___x_2860_, 1, v_a_2795_);
                    v___x_2861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2860_);
                    v___x_2862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
                    return v___x_2862_;
                }
            }
            1 => {
                v___x_2815_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2815_, 0, v_val_2811_);
                crate::leanh::lean_ctor_set(v___x_2815_, 1, v_a_2795_);
                if v_isShared_2814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2813_, 0, v___x_2815_);
                    v___x_2817_ = v___x_2813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2815_);
                    v___x_2817_ = v_reuseFailAlloc_2819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2818_, 0, v___x_2817_);
                return v___x_2818_;
            }
            3 => {
                v_val_2826_ = crate::leanh::lean_ctor_get(v_a_2822_, 0);
                v_isSharedCheck_2857_ = (!crate::leanh::lean_is_exclusive(v_a_2822_)) as u8;
                if v_isSharedCheck_2857_ == 0 {
                    v___x_2828_ = v_a_2822_;
                    v_isShared_2829_ = v_isSharedCheck_2857_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2826_);
                    crate::leanh::lean_dec(v_a_2822_);
                    v___x_2828_ = crate::leanh::lean_box(0);
                    v_isShared_2829_ = v_isSharedCheck_2857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_2830_ = crate::leanh::lean_ctor_get(v_val_2826_, 1);
                v_fst_2831_ = crate::leanh::lean_ctor_get(v_val_2826_, 0);
                v_isSharedCheck_2856_ = (!crate::leanh::lean_is_exclusive(v_val_2826_)) as u8;
                if v_isSharedCheck_2856_ == 0 {
                    v___x_2833_ = v_val_2826_;
                    v_isShared_2834_ = v_isSharedCheck_2856_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2830_);
                    crate::leanh::lean_inc(v_fst_2831_);
                    crate::leanh::lean_dec(v_val_2826_);
                    v___x_2833_ = crate::leanh::lean_box(0);
                    v_isShared_2834_ = v_isSharedCheck_2856_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_cache_2835_ = crate::leanh::lean_ctor_get(v_snd_2830_, 0);
                v_varTypes_2836_ = crate::leanh::lean_ctor_get(v_snd_2830_, 1);
                v_lhss_2837_ = crate::leanh::lean_ctor_get(v_snd_2830_, 2);
                v_rhss_2838_ = crate::leanh::lean_ctor_get(v_snd_2830_, 3);
                v_isSharedCheck_2855_ = (!crate::leanh::lean_is_exclusive(v_snd_2830_)) as u8;
                if v_isSharedCheck_2855_ == 0 {
                    v___x_2840_ = v_snd_2830_;
                    v_isShared_2841_ = v_isSharedCheck_2855_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhss_2838_);
                    crate::leanh::lean_inc(v_lhss_2837_);
                    crate::leanh::lean_inc(v_varTypes_2836_);
                    crate::leanh::lean_inc(v_cache_2835_);
                    crate::leanh::lean_dec(v_snd_2830_);
                    v___x_2840_ = crate::leanh::lean_box(0);
                    v_isShared_2841_ = v_isSharedCheck_2855_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc(v_fst_2831_);
                v___x_2842_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_2835_, v___x_2809_, v_fst_2831_);
                if v_isShared_2841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2840_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_varTypes_2836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_lhss_2837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_rhss_2838_);
                    v___x_2844_ = v_reuseFailAlloc_2854_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2834_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2833_, 1, v___x_2844_);
                    v___x_2846_ = v___x_2833_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2853_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_fst_2831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2844_);
                    v___x_2846_ = v_reuseFailAlloc_2853_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2829_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2828_, 0, v___x_2846_);
                    v___x_2848_ = v___x_2828_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2846_);
                    v___x_2848_ = v_reuseFailAlloc_2852_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2848_);
                    v___x_2850_ = v___x_2824_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
                    v___x_2850_ = v_reuseFailAlloc_2851_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go___boxed(
    mut v_lhs_2863_: *mut crate::leanh::LeanObject,
    mut v_rhs_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
    mut v_a_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_2863_, v_rhs_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
    crate::leanh::lean_dec(v_a_2876_);
    crate::leanh::lean_dec_ref(v_a_2875_);
    crate::leanh::lean_dec(v_a_2874_);
    crate::leanh::lean_dec_ref(v_a_2873_);
    crate::leanh::lean_dec(v_a_2872_);
    crate::leanh::lean_dec_ref(v_a_2871_);
    crate::leanh::lean_dec(v_a_2870_);
    crate::leanh::lean_dec_ref(v_a_2869_);
    crate::leanh::lean_dec(v_a_2868_);
    crate::leanh::lean_dec(v_a_2867_);
    crate::leanh::lean_dec(v_a_2865_);
    return v_res_2878_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(
    mut v_lhs_2879_: *mut crate::leanh::LeanObject,
    mut v_rhs_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
    mut v_a_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
    mut v_a_2884_: *mut crate::leanh::LeanObject,
    mut v_a_2885_: *mut crate::leanh::LeanObject,
    mut v_a_2886_: *mut crate::leanh::LeanObject,
    mut v_a_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
    mut v_a_2890_: *mut crate::leanh::LeanObject,
    mut v_a_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2894_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_2879_, v_rhs_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
    crate::leanh::lean_dec(v_a_2892_);
    crate::leanh::lean_dec_ref(v_a_2891_);
    crate::leanh::lean_dec(v_a_2890_);
    crate::leanh::lean_dec_ref(v_a_2889_);
    crate::leanh::lean_dec(v_a_2888_);
    crate::leanh::lean_dec_ref(v_a_2887_);
    crate::leanh::lean_dec(v_a_2886_);
    crate::leanh::lean_dec_ref(v_a_2885_);
    crate::leanh::lean_dec(v_a_2884_);
    crate::leanh::lean_dec(v_a_2883_);
    crate::leanh::lean_dec(v_a_2881_);
    return v_res_2894_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(
    mut v_00_u03b2_2895_: *mut crate::leanh::LeanObject,
    mut v_m_2896_: *mut crate::leanh::LeanObject,
    mut v_a_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_2896_, v_a_2897_);
    return v___x_2898_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(
    mut v_00_u03b2_2899_: *mut crate::leanh::LeanObject,
    mut v_m_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(v_00_u03b2_2899_, v_m_2900_, v_a_2901_);
    crate::leanh::lean_dec_ref(v_a_2901_);
    crate::leanh::lean_dec_ref(v_m_2900_);
    return v_res_2902_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(
    mut v_00_u03b2_2903_: *mut crate::leanh::LeanObject,
    mut v_m_2904_: *mut crate::leanh::LeanObject,
    mut v_a_2905_: *mut crate::leanh::LeanObject,
    mut v_b_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_2904_, v_a_2905_, v_b_2906_);
    return v___x_2907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(
    mut v_00_u03b2_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_x_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2911_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_2909_, v_x_2910_);
    return v___x_2911_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(
    mut v_00_u03b2_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
    mut v_x_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(v_00_u03b2_2912_, v_a_2913_, v_x_2914_);
    crate::leanh::lean_dec(v_x_2914_);
    crate::leanh::lean_dec_ref(v_a_2913_);
    return v_res_2915_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(
    mut v_00_u03b2_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
    mut v_x_2918_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2919_: u8 = 0;
    v___x_2919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_2917_, v_x_2918_);
    return v___x_2919_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(
    mut v_00_u03b2_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_x_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2923_: u8 = 0;
    let mut v_r_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_2920_, v_a_2921_, v_x_2922_);
    crate::leanh::lean_dec(v_x_2922_);
    crate::leanh::lean_dec_ref(v_a_2921_);
    v_r_2924_ = crate::leanh::lean_box((v_res_2923_) as usize);
    return v_r_2924_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(
    mut v_00_u03b2_2925_: *mut crate::leanh::LeanObject,
    mut v_data_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_data_2926_);
    return v___x_2927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(
    mut v_00_u03b2_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_b_2930_: *mut crate::leanh::LeanObject,
    mut v_x_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_2929_, v_b_2930_, v_x_2931_);
    return v___x_2932_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2933_: *mut crate::leanh::LeanObject,
    mut v_i_2934_: *mut crate::leanh::LeanObject,
    mut v_source_2935_: *mut crate::leanh::LeanObject,
    mut v_target_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v_i_2934_, v_source_2935_, v_target_2936_);
    return v___x_2937_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2938_: *mut crate::leanh::LeanObject,
    mut v_x_2939_: *mut crate::leanh::LeanObject,
    mut v_x_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_x_2939_, v_x_2940_);
    return v___x_2941_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2942_ = crate::leanh::lean_box(0);
    v___x_2943_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2944_ = lean_mk_array(v___x_2943_, v___x_2942_);
    return v___x_2944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
    v___x_2946_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2947_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2947_, 0, v___x_2946_);
    crate::leanh::lean_ctor_set(v___x_2947_, 1, v___x_2945_);
    return v___x_2947_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2950_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2;
    v___x_2951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
    v___x_2952_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2952_, 0, v___x_2951_);
    crate::leanh::lean_ctor_set(v___x_2952_, 1, v___x_2950_);
    crate::leanh::lean_ctor_set(v___x_2952_, 2, v___x_2950_);
    crate::leanh::lean_ctor_set(v___x_2952_, 3, v___x_2950_);
    return v___x_2952_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(
    mut v_lhs_2960_: *mut crate::leanh::LeanObject,
    mut v_rhs_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v_val_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2987_: u8 = 0;
    let mut v_snd_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v_varTypes_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhss_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhss_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v_a_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_a_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_a_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v_a_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3069_: u8 = 0;
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2973_ = l_Lean_Meta_Sym_shareCommon___redArg(v_lhs_2960_, v_a_2967_);
                if crate::leanh::lean_obj_tag(v___x_2973_) == 0 {
                    v_a_2974_ = crate::leanh::lean_ctor_get(v___x_2973_, 0);
                    crate::leanh::lean_inc(v_a_2974_);
                    crate::leanh::lean_dec_ref_known(v___x_2973_, 1);
                    v___x_2975_ = l_Lean_Meta_Sym_shareCommon___redArg(v_rhs_2961_, v_a_2967_);
                    if crate::leanh::lean_obj_tag(v___x_2975_) == 0 {
                        v_a_2976_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                        crate::leanh::lean_inc(v_a_2976_);
                        crate::leanh::lean_dec_ref_known(v___x_2975_, 1);
                        v___x_2977_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2978_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
                        v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_2974_, v_a_2976_, v___x_2977_, v___x_2978_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
                        if crate::leanh::lean_obj_tag(v___x_2979_) == 0 {
                            v_a_2980_ = crate::leanh::lean_ctor_get(v___x_2979_, 0);
                            v_isSharedCheck_3049_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2979_)) as u8;
                            if v_isSharedCheck_3049_ == 0 {
                                v___x_2982_ = v___x_2979_;
                                v_isShared_2983_ = v_isSharedCheck_3049_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2980_);
                                crate::leanh::lean_dec(v___x_2979_);
                                v___x_2982_ = crate::leanh::lean_box(0);
                                v_isShared_2983_ = v_isSharedCheck_3049_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3050_ = crate::leanh::lean_ctor_get(v___x_2979_, 0);
                            v_isSharedCheck_3057_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2979_)) as u8;
                            if v_isSharedCheck_3057_ == 0 {
                                v___x_3052_ = v___x_2979_;
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3050_);
                                crate::leanh::lean_dec(v___x_2979_);
                                v___x_3052_ = crate::leanh::lean_box(0);
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2974_);
                        v_a_3058_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                        v_isSharedCheck_3065_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                        if v_isSharedCheck_3065_ == 0 {
                            v___x_3060_ = v___x_2975_;
                            v_isShared_3061_ = v_isSharedCheck_3065_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3058_);
                            crate::leanh::lean_dec(v___x_2975_);
                            v___x_3060_ = crate::leanh::lean_box(0);
                            v_isShared_3061_ = v_isSharedCheck_3065_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_2961_);
                    v_a_3066_ = crate::leanh::lean_ctor_get(v___x_2973_, 0);
                    v_isSharedCheck_3073_ = (!crate::leanh::lean_is_exclusive(v___x_2973_)) as u8;
                    if v_isSharedCheck_3073_ == 0 {
                        v___x_3068_ = v___x_2973_;
                        v_isShared_3069_ = v_isSharedCheck_3073_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3066_);
                        crate::leanh::lean_dec(v___x_2973_);
                        v___x_3068_ = crate::leanh::lean_box(0);
                        v_isShared_3069_ = v_isSharedCheck_3073_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2980_) == 1 {
                    v_val_2984_ = crate::leanh::lean_ctor_get(v_a_2980_, 0);
                    v_isSharedCheck_3044_ = (!crate::leanh::lean_is_exclusive(v_a_2980_)) as u8;
                    if v_isSharedCheck_3044_ == 0 {
                        v___x_2986_ = v_a_2980_;
                        v_isShared_2987_ = v_isSharedCheck_3044_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2984_);
                        crate::leanh::lean_dec(v_a_2980_);
                        v___x_2986_ = crate::leanh::lean_box(0);
                        v_isShared_2987_ = v_isSharedCheck_3044_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2980_);
                    v___x_3045_ = crate::leanh::lean_box(0);
                    if v_isShared_2983_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2982_, 0, v___x_3045_);
                        v___x_3047_ = v___x_2982_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
                        v___x_3047_ = v_reuseFailAlloc_3048_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_2988_ = crate::leanh::lean_ctor_get(v_val_2984_, 1);
                v_fst_2989_ = crate::leanh::lean_ctor_get(v_val_2984_, 0);
                v_isSharedCheck_3043_ = (!crate::leanh::lean_is_exclusive(v_val_2984_)) as u8;
                if v_isSharedCheck_3043_ == 0 {
                    v___x_2991_ = v_val_2984_;
                    v_isShared_2992_ = v_isSharedCheck_3043_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2988_);
                    crate::leanh::lean_inc(v_fst_2989_);
                    crate::leanh::lean_dec(v_val_2984_);
                    v___x_2991_ = crate::leanh::lean_box(0);
                    v_isShared_2992_ = v_isSharedCheck_3043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_varTypes_2993_ = crate::leanh::lean_ctor_get(v_snd_2988_, 1);
                crate::leanh::lean_inc_ref(v_varTypes_2993_);
                v_lhss_2994_ = crate::leanh::lean_ctor_get(v_snd_2988_, 2);
                crate::leanh::lean_inc_ref(v_lhss_2994_);
                v_rhss_2995_ = crate::leanh::lean_ctor_get(v_snd_2988_, 3);
                crate::leanh::lean_inc_ref(v_rhss_2995_);
                crate::leanh::lean_dec(v_snd_2988_);
                v___x_2996_ = lean_array_get_size(v_lhss_2994_);
                v___x_2997_ = lean_nat_dec_eq(v___x_2996_, v___x_2977_);
                if v___x_2997_ == 0 {
                    crate::leanh::lean_del_object(v___x_2982_);
                    v___x_2998_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_2993_, v_fst_2989_);
                    crate::leanh::lean_dec_ref(v_varTypes_2993_);
                    crate::leanh::lean_inc(v_a_2971_);
                    crate::leanh::lean_inc_ref(v_a_2970_);
                    crate::leanh::lean_inc(v_a_2969_);
                    crate::leanh::lean_inc_ref(v_a_2968_);
                    crate::leanh::lean_inc_ref(v___x_2998_);
                    v___x_2999_ =
                        lean_infer_type(v___x_2998_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
                    if crate::leanh::lean_obj_tag(v___x_2999_) == 0 {
                        v_a_3000_ = crate::leanh::lean_ctor_get(v___x_2999_, 0);
                        crate::leanh::lean_inc_n(v_a_3000_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2999_, 1);
                        v___x_3001_ = l_Lean_Meta_getLevel(
                            v_a_3000_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3001_) == 0 {
                            v_a_3002_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                            v_isSharedCheck_3022_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3001_)) as u8;
                            if v_isSharedCheck_3022_ == 0 {
                                v___x_3004_ = v___x_3001_;
                                v_isShared_3005_ = v_isSharedCheck_3022_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3002_);
                                crate::leanh::lean_dec(v___x_3001_);
                                v___x_3004_ = crate::leanh::lean_box(0);
                                v_isShared_3005_ = v_isSharedCheck_3022_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3000_);
                            crate::leanh::lean_dec_ref(v___x_2998_);
                            crate::leanh::lean_dec_ref(v_rhss_2995_);
                            crate::leanh::lean_dec_ref(v_lhss_2994_);
                            crate::leanh::lean_del_object(v___x_2991_);
                            crate::leanh::lean_del_object(v___x_2986_);
                            v_a_3023_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                            v_isSharedCheck_3030_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3001_)) as u8;
                            if v_isSharedCheck_3030_ == 0 {
                                v___x_3025_ = v___x_3001_;
                                v_isShared_3026_ = v_isSharedCheck_3030_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3023_);
                                crate::leanh::lean_dec(v___x_3001_);
                                v___x_3025_ = crate::leanh::lean_box(0);
                                v_isShared_3026_ = v_isSharedCheck_3030_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2998_);
                        crate::leanh::lean_dec_ref(v_rhss_2995_);
                        crate::leanh::lean_dec_ref(v_lhss_2994_);
                        crate::leanh::lean_del_object(v___x_2991_);
                        crate::leanh::lean_del_object(v___x_2986_);
                        v_a_3031_ = crate::leanh::lean_ctor_get(v___x_2999_, 0);
                        v_isSharedCheck_3038_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2999_)) as u8;
                        if v_isSharedCheck_3038_ == 0 {
                            v___x_3033_ = v___x_2999_;
                            v_isShared_3034_ = v_isSharedCheck_3038_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3031_);
                            crate::leanh::lean_dec(v___x_2999_);
                            v___x_3033_ = crate::leanh::lean_box(0);
                            v_isShared_3034_ = v_isSharedCheck_3038_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhss_2995_);
                    crate::leanh::lean_dec_ref(v_lhss_2994_);
                    crate::leanh::lean_dec_ref(v_varTypes_2993_);
                    crate::leanh::lean_del_object(v___x_2991_);
                    crate::leanh::lean_dec(v_fst_2989_);
                    crate::leanh::lean_del_object(v___x_2986_);
                    v___x_3039_ = crate::leanh::lean_box(0);
                    if v_isShared_2983_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2982_, 0, v___x_3039_);
                        v___x_3041_ = v___x_2982_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
                        v___x_3041_ = v_reuseFailAlloc_3042_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3006_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7;
                v___x_3007_ = crate::leanh::lean_box(0);
                v___x_3008_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3008_, 0, v_a_3002_);
                crate::leanh::lean_ctor_set(v___x_3008_, 1, v___x_3007_);
                v___x_3009_ = l_Lean_Expr_const___override(v___x_3006_, v___x_3008_);
                v___x_3010_ = l_Lean_mkAppB(v___x_3009_, v_a_3000_, v___x_2998_);
                crate::leanh::lean_inc_ref(v___x_3010_);
                v___x_3011_ = l_Lean_mkAppN(v___x_3010_, v_lhss_2994_);
                crate::leanh::lean_dec_ref(v_lhss_2994_);
                v___x_3012_ = l_Lean_mkAppN(v___x_3010_, v_rhss_2995_);
                crate::leanh::lean_dec_ref(v_rhss_2995_);
                if v_isShared_2992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2991_, 1, v___x_3012_);
                    crate::leanh::lean_ctor_set(v___x_2991_, 0, v___x_3011_);
                    v___x_3014_ = v___x_2991_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3012_);
                    v___x_3014_ = v_reuseFailAlloc_3021_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2986_, 0, v___x_3014_);
                    v___x_3016_ = v___x_2986_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3014_);
                    v___x_3016_ = v_reuseFailAlloc_3020_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3004_, 0, v___x_3016_);
                    v___x_3018_ = v___x_3004_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
                    v___x_3018_ = v_reuseFailAlloc_3019_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3018_;
            }
            8 => {
                if v_isShared_3026_ == 0 {
                    v___x_3028_ = v___x_3025_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
                    v___x_3028_ = v_reuseFailAlloc_3029_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3028_;
            }
            10 => {
                if v_isShared_3034_ == 0 {
                    v___x_3036_ = v___x_3033_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
                    v___x_3036_ = v_reuseFailAlloc_3037_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3036_;
            }
            12 => {
                return v___x_3041_;
            }
            13 => {
                return v___x_3047_;
            }
            14 => {
                if v_isShared_3053_ == 0 {
                    v___x_3055_ = v___x_3052_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
                    v___x_3055_ = v_reuseFailAlloc_3056_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3055_;
            }
            16 => {
                if v_isShared_3061_ == 0 {
                    v___x_3063_ = v___x_3060_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
                    v___x_3063_ = v_reuseFailAlloc_3064_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3063_;
            }
            18 => {
                if v_isShared_3069_ == 0 {
                    v___x_3071_ = v___x_3068_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
                    v___x_3071_ = v_reuseFailAlloc_3072_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___boxed(
    mut v_lhs_3074_: *mut crate::leanh::LeanObject,
    mut v_rhs_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
    mut v_a_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ =
        l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(
            v_lhs_3074_,
            v_rhs_3075_,
            v_a_3076_,
            v_a_3077_,
            v_a_3078_,
            v_a_3079_,
            v_a_3080_,
            v_a_3081_,
            v_a_3082_,
            v_a_3083_,
            v_a_3084_,
            v_a_3085_,
        );
    crate::leanh::lean_dec(v_a_3085_);
    crate::leanh::lean_dec_ref(v_a_3084_);
    crate::leanh::lean_dec(v_a_3083_);
    crate::leanh::lean_dec_ref(v_a_3082_);
    crate::leanh::lean_dec(v_a_3081_);
    crate::leanh::lean_dec_ref(v_a_3080_);
    crate::leanh::lean_dec(v_a_3079_);
    crate::leanh::lean_dec_ref(v_a_3078_);
    crate::leanh::lean_dec(v_a_3077_);
    crate::leanh::lean_dec(v_a_3076_);
    return v_res_3087_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(
    mut v_msgData_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3094_ = lean_st_ref_get(v___y_3092_);
    v_env_3095_ = crate::leanh::lean_ctor_get(v___x_3094_, 0);
    crate::leanh::lean_inc_ref(v_env_3095_);
    crate::leanh::lean_dec(v___x_3094_);
    v___x_3096_ = lean_st_ref_get(v___y_3090_);
    v_mctx_3097_ = crate::leanh::lean_ctor_get(v___x_3096_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3097_);
    crate::leanh::lean_dec(v___x_3096_);
    v_lctx_3098_ = crate::leanh::lean_ctor_get(v___y_3089_, 2);
    v_options_3099_ = crate::leanh::lean_ctor_get(v___y_3091_, 2);
    crate::leanh::lean_inc_ref(v_options_3099_);
    crate::leanh::lean_inc_ref(v_lctx_3098_);
    v___x_3100_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3100_, 0, v_env_3095_);
    crate::leanh::lean_ctor_set(v___x_3100_, 1, v_mctx_3097_);
    crate::leanh::lean_ctor_set(v___x_3100_, 2, v_lctx_3098_);
    crate::leanh::lean_ctor_set(v___x_3100_, 3, v_options_3099_);
    v___x_3101_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3101_, 0, v___x_3100_);
    crate::leanh::lean_ctor_set(v___x_3101_, 1, v_msgData_3088_);
    v___x_3102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3102_, 0, v___x_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(
    mut v_msgData_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
    crate::leanh::lean_dec(v___y_3107_);
    crate::leanh::lean_dec_ref(v___y_3106_);
    crate::leanh::lean_dec(v___y_3105_);
    crate::leanh::lean_dec_ref(v___y_3104_);
    return v_res_3109_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: f64 = 0.0;
    v___x_3110_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3111_ = lean_float_of_nat(v___x_3110_);
    return v___x_3111_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(
    mut v_cls_3115_: *mut crate::leanh::LeanObject,
    mut v_msg_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3140_: u8 = 0;
    let mut v_tid_3141_: u64 = 0;
    let mut v_traces_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: f64 = 0.0;
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3166_: u8 = 0;
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3122_ = crate::leanh::lean_ctor_get(v___y_3119_, 5);
                v___x_3123_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
                v_a_3124_ = crate::leanh::lean_ctor_get(v___x_3123_, 0);
                v_isSharedCheck_3168_ = (!crate::leanh::lean_is_exclusive(v___x_3123_)) as u8;
                if v_isSharedCheck_3168_ == 0 {
                    v___x_3126_ = v___x_3123_;
                    v_isShared_3127_ = v_isSharedCheck_3168_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3124_);
                    crate::leanh::lean_dec(v___x_3123_);
                    v___x_3126_ = crate::leanh::lean_box(0);
                    v_isShared_3127_ = v_isSharedCheck_3168_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3128_ = lean_st_ref_take(v___y_3120_);
                v_traceState_3129_ = crate::leanh::lean_ctor_get(v___x_3128_, 4);
                v_env_3130_ = crate::leanh::lean_ctor_get(v___x_3128_, 0);
                v_nextMacroScope_3131_ = crate::leanh::lean_ctor_get(v___x_3128_, 1);
                v_ngen_3132_ = crate::leanh::lean_ctor_get(v___x_3128_, 2);
                v_auxDeclNGen_3133_ = crate::leanh::lean_ctor_get(v___x_3128_, 3);
                v_cache_3134_ = crate::leanh::lean_ctor_get(v___x_3128_, 5);
                v_messages_3135_ = crate::leanh::lean_ctor_get(v___x_3128_, 6);
                v_infoState_3136_ = crate::leanh::lean_ctor_get(v___x_3128_, 7);
                v_snapshotTasks_3137_ = crate::leanh::lean_ctor_get(v___x_3128_, 8);
                v_isSharedCheck_3167_ = (!crate::leanh::lean_is_exclusive(v___x_3128_)) as u8;
                if v_isSharedCheck_3167_ == 0 {
                    v___x_3139_ = v___x_3128_;
                    v_isShared_3140_ = v_isSharedCheck_3167_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3137_);
                    crate::leanh::lean_inc(v_infoState_3136_);
                    crate::leanh::lean_inc(v_messages_3135_);
                    crate::leanh::lean_inc(v_cache_3134_);
                    crate::leanh::lean_inc(v_traceState_3129_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3133_);
                    crate::leanh::lean_inc(v_ngen_3132_);
                    crate::leanh::lean_inc(v_nextMacroScope_3131_);
                    crate::leanh::lean_inc(v_env_3130_);
                    crate::leanh::lean_dec(v___x_3128_);
                    v___x_3139_ = crate::leanh::lean_box(0);
                    v_isShared_3140_ = v_isSharedCheck_3167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3141_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3129_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3142_ = crate::leanh::lean_ctor_get(v_traceState_3129_, 0);
                v_isSharedCheck_3166_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3129_)) as u8;
                if v_isSharedCheck_3166_ == 0 {
                    v___x_3144_ = v_traceState_3129_;
                    v_isShared_3145_ = v_isSharedCheck_3166_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3142_);
                    crate::leanh::lean_dec(v_traceState_3129_);
                    v___x_3144_ = crate::leanh::lean_box(0);
                    v_isShared_3145_ = v_isSharedCheck_3166_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3146_ = crate::leanh::lean_box(0);
                v___x_3147_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
                v___x_3148_ = 0;
                v___x_3149_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1;
                v___x_3150_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3150_, 0, v_cls_3115_);
                crate::leanh::lean_ctor_set(v___x_3150_, 1, v___x_3146_);
                crate::leanh::lean_ctor_set(v___x_3150_, 2, v___x_3149_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3147_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3147_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3148_,
                );
                v___x_3151_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2;
                v___x_3152_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3150_);
                crate::leanh::lean_ctor_set(v___x_3152_, 1, v_a_3124_);
                crate::leanh::lean_ctor_set(v___x_3152_, 2, v___x_3151_);
                crate::leanh::lean_inc(v_ref_3122_);
                v___x_3153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3153_, 0, v_ref_3122_);
                crate::leanh::lean_ctor_set(v___x_3153_, 1, v___x_3152_);
                v___x_3154_ = l_Lean_PersistentArray_push___redArg(v_traces_3142_, v___x_3153_);
                if v_isShared_3145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3144_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3144_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3154_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3165_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3141_,
                    );
                    v___x_3156_ = v_reuseFailAlloc_3165_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3140_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3139_, 4, v___x_3156_);
                    v___x_3158_ = v___x_3139_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_env_3130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_nextMacroScope_3131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_ngen_3132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_auxDeclNGen_3133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 4, v___x_3156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 5, v_cache_3134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 6, v_messages_3135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 7, v_infoState_3136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 8, v_snapshotTasks_3137_);
                    v___x_3158_ = v_reuseFailAlloc_3164_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3159_ = lean_st_ref_set(v___y_3120_, v___x_3158_);
                v___x_3160_ = crate::leanh::lean_box(0);
                if v_isShared_3127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3126_, 0, v___x_3160_);
                    v___x_3162_ = v___x_3126_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
                    v___x_3162_ = v_reuseFailAlloc_3163_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___boxed(
    mut v_cls_3169_: *mut crate::leanh::LeanObject,
    mut v_msg_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_3169_, v_msg_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
    crate::leanh::lean_dec(v___y_3174_);
    crate::leanh::lean_dec_ref(v___y_3173_);
    crate::leanh::lean_dec(v___y_3172_);
    crate::leanh::lean_dec_ref(v___y_3171_);
    return v_res_3176_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
    v___x_3188_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5;
    v___x_3189_ = l_Lean_Name_append(v___x_3188_, v___x_3187_);
    return v___x_3189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
    v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
    return v___x_3192_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
    v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
    return v___x_3195_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3197_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11;
    v___x_3198_ = l_Lean_stringToMessageData(v___x_3197_);
    return v___x_3198_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(
    mut v_lhs_u2080_3199_: *mut crate::leanh::LeanObject,
    mut v_rhs_u2080_3200_: *mut crate::leanh::LeanObject,
    mut v_a_3201_: *mut crate::leanh::LeanObject,
    mut v_a_3202_: *mut crate::leanh::LeanObject,
    mut v_a_3203_: *mut crate::leanh::LeanObject,
    mut v_a_3204_: *mut crate::leanh::LeanObject,
    mut v_a_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_a_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v_val_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v_fst_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___y_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3246_: u8 = 0;
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_a_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_a_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v_a_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_a_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_options_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3306_: u8 = 0;
    let mut v_inheritedTraceOptions_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut v_reuseFailAlloc_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v_a_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3212_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_3199_, v_rhs_u2080_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
                if crate::leanh::lean_obj_tag(v___x_3212_) == 0 {
                    v_a_3213_ = crate::leanh::lean_ctor_get(v___x_3212_, 0);
                    v_isSharedCheck_3337_ = (!crate::leanh::lean_is_exclusive(v___x_3212_)) as u8;
                    if v_isSharedCheck_3337_ == 0 {
                        v___x_3215_ = v___x_3212_;
                        v_isShared_3216_ = v_isSharedCheck_3337_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3213_);
                        crate::leanh::lean_dec(v___x_3212_);
                        v___x_3215_ = crate::leanh::lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3337_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3338_ = crate::leanh::lean_ctor_get(v___x_3212_, 0);
                    v_isSharedCheck_3345_ = (!crate::leanh::lean_is_exclusive(v___x_3212_)) as u8;
                    if v_isSharedCheck_3345_ == 0 {
                        v___x_3340_ = v___x_3212_;
                        v_isShared_3341_ = v_isSharedCheck_3345_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3338_);
                        crate::leanh::lean_dec(v___x_3212_);
                        v___x_3340_ = crate::leanh::lean_box(0);
                        v_isShared_3341_ = v_isSharedCheck_3345_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3213_) == 1 {
                    crate::leanh::lean_del_object(v___x_3215_);
                    v_val_3217_ = crate::leanh::lean_ctor_get(v_a_3213_, 0);
                    v_isSharedCheck_3332_ = (!crate::leanh::lean_is_exclusive(v_a_3213_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3219_ = v_a_3213_;
                        v_isShared_3220_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3217_);
                        crate::leanh::lean_dec(v_a_3213_);
                        v___x_3219_ = crate::leanh::lean_box(0);
                        v_isShared_3220_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3213_);
                    v___x_3333_ = crate::leanh::lean_box(0);
                    if v_isShared_3216_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3333_);
                        v___x_3335_ = v___x_3215_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
                        v___x_3335_ = v_reuseFailAlloc_3336_;
                        state = 23;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3221_ = crate::leanh::lean_ctor_get(v_val_3217_, 0);
                v_snd_3222_ = crate::leanh::lean_ctor_get(v_val_3217_, 1);
                v_isSharedCheck_3331_ = (!crate::leanh::lean_is_exclusive(v_val_3217_)) as u8;
                if v_isSharedCheck_3331_ == 0 {
                    v___x_3224_ = v_val_3217_;
                    v_isShared_3225_ = v_isSharedCheck_3331_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3222_);
                    crate::leanh::lean_inc(v_fst_3221_);
                    crate::leanh::lean_dec(v_val_3217_);
                    v___x_3224_ = crate::leanh::lean_box(0);
                    v_isShared_3225_ = v_isSharedCheck_3331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_options_3305_ = crate::leanh::lean_ctor_get(v_a_3209_, 2);
                v_hasTrace_3306_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3305_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3306_ == 0 {
                    crate::leanh::lean_del_object(v___x_3224_);
                    v___y_3227_ = v_a_3201_;
                    v___y_3228_ = v_a_3202_;
                    v___y_3229_ = v_a_3203_;
                    v___y_3230_ = v_a_3204_;
                    v___y_3231_ = v_a_3205_;
                    v___y_3232_ = v_a_3206_;
                    v___y_3233_ = v_a_3207_;
                    v___y_3234_ = v_a_3208_;
                    v___y_3235_ = v_a_3209_;
                    v___y_3236_ = v_a_3210_;
                    state = 4;
                    continue;
                } else {
                    v_inheritedTraceOptions_3307_ = crate::leanh::lean_ctor_get(v_a_3209_, 13);
                    v___x_3308_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
                    v___x_3309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
                    v___x_3310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3307_,
                        v_options_3305_,
                        v___x_3309_,
                    );
                    if v___x_3310_ == 0 {
                        crate::leanh::lean_del_object(v___x_3224_);
                        v___y_3227_ = v_a_3201_;
                        v___y_3228_ = v_a_3202_;
                        v___y_3229_ = v_a_3203_;
                        v___y_3230_ = v_a_3204_;
                        v___y_3231_ = v_a_3205_;
                        v___y_3232_ = v_a_3206_;
                        v___y_3233_ = v_a_3207_;
                        v___y_3234_ = v_a_3208_;
                        v___y_3235_ = v_a_3209_;
                        v___y_3236_ = v_a_3210_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
                        crate::leanh::lean_inc(v_fst_3221_);
                        v___x_3312_ = l_Lean_MessageData_ofExpr(v_fst_3221_);
                        if v_isShared_3225_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3224_, 7);
                            crate::leanh::lean_ctor_set(v___x_3224_, 1, v___x_3312_);
                            crate::leanh::lean_ctor_set(v___x_3224_, 0, v___x_3311_);
                            v___x_3314_ = v___x_3224_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_3330_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3311_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___x_3312_);
                            v___x_3314_ = v_reuseFailAlloc_3330_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_3237_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_3221_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
                if crate::leanh::lean_obj_tag(v___x_3237_) == 0 {
                    v_a_3238_ = crate::leanh::lean_ctor_get(v___x_3237_, 0);
                    crate::leanh::lean_inc(v_a_3238_);
                    crate::leanh::lean_dec_ref_known(v___x_3237_, 1);
                    v___x_3239_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_3222_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
                    if crate::leanh::lean_obj_tag(v___x_3239_) == 0 {
                        v_a_3240_ = crate::leanh::lean_ctor_get(v___x_3239_, 0);
                        crate::leanh::lean_inc(v_a_3240_);
                        crate::leanh::lean_dec_ref_known(v___x_3239_, 1);
                        crate::leanh::lean_inc(v___y_3236_);
                        crate::leanh::lean_inc_ref(v___y_3235_);
                        crate::leanh::lean_inc(v___y_3234_);
                        crate::leanh::lean_inc_ref(v___y_3233_);
                        crate::leanh::lean_inc(v___y_3232_);
                        crate::leanh::lean_inc_ref(v___y_3231_);
                        crate::leanh::lean_inc(v___y_3230_);
                        crate::leanh::lean_inc_ref(v___y_3229_);
                        crate::leanh::lean_inc(v___y_3228_);
                        crate::leanh::lean_inc(v___y_3227_);
                        v___x_3241_ = lean_grind_process_new_facts(
                            v___y_3227_,
                            v___y_3228_,
                            v___y_3229_,
                            v___y_3230_,
                            v___y_3231_,
                            v___y_3232_,
                            v___y_3233_,
                            v___y_3234_,
                            v___y_3235_,
                            v___y_3236_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3241_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3241_, 1);
                            v___x_3242_ =
                                l_Lean_Meta_Grind_isEqv___redArg(v_a_3238_, v_a_3240_, v___y_3227_);
                            if crate::leanh::lean_obj_tag(v___x_3242_) == 0 {
                                v_a_3243_ = crate::leanh::lean_ctor_get(v___x_3242_, 0);
                                v_isSharedCheck_3272_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3242_)) as u8;
                                if v_isSharedCheck_3272_ == 0 {
                                    v___x_3245_ = v___x_3242_;
                                    v_isShared_3246_ = v_isSharedCheck_3272_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3243_);
                                    crate::leanh::lean_dec(v___x_3242_);
                                    v___x_3245_ = crate::leanh::lean_box(0);
                                    v_isShared_3246_ = v_isSharedCheck_3272_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3240_);
                                crate::leanh::lean_dec(v_a_3238_);
                                crate::leanh::lean_del_object(v___x_3219_);
                                v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3242_, 0);
                                v_isSharedCheck_3280_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3242_)) as u8;
                                if v_isSharedCheck_3280_ == 0 {
                                    v___x_3275_ = v___x_3242_;
                                    v_isShared_3276_ = v_isSharedCheck_3280_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3273_);
                                    crate::leanh::lean_dec(v___x_3242_);
                                    v___x_3275_ = crate::leanh::lean_box(0);
                                    v_isShared_3276_ = v_isSharedCheck_3280_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3240_);
                            crate::leanh::lean_dec(v_a_3238_);
                            crate::leanh::lean_del_object(v___x_3219_);
                            v_a_3281_ = crate::leanh::lean_ctor_get(v___x_3241_, 0);
                            v_isSharedCheck_3288_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3241_)) as u8;
                            if v_isSharedCheck_3288_ == 0 {
                                v___x_3283_ = v___x_3241_;
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3281_);
                                crate::leanh::lean_dec(v___x_3241_);
                                v___x_3283_ = crate::leanh::lean_box(0);
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3238_);
                        crate::leanh::lean_del_object(v___x_3219_);
                        v_a_3289_ = crate::leanh::lean_ctor_get(v___x_3239_, 0);
                        v_isSharedCheck_3296_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3239_)) as u8;
                        if v_isSharedCheck_3296_ == 0 {
                            v___x_3291_ = v___x_3239_;
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3289_);
                            crate::leanh::lean_dec(v___x_3239_);
                            v___x_3291_ = crate::leanh::lean_box(0);
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3222_);
                    crate::leanh::lean_del_object(v___x_3219_);
                    v_a_3297_ = crate::leanh::lean_ctor_get(v___x_3237_, 0);
                    v_isSharedCheck_3304_ = (!crate::leanh::lean_is_exclusive(v___x_3237_)) as u8;
                    if v_isSharedCheck_3304_ == 0 {
                        v___x_3299_ = v___x_3237_;
                        v_isShared_3300_ = v_isSharedCheck_3304_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3297_);
                        crate::leanh::lean_dec(v___x_3237_);
                        v___x_3299_ = crate::leanh::lean_box(0);
                        v_isShared_3300_ = v_isSharedCheck_3304_;
                        state = 18;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3247_ = (crate::leanh::lean_unbox(v_a_3243_) as u8);
                crate::leanh::lean_dec(v_a_3243_);
                if v___x_3247_ == 0 {
                    crate::leanh::lean_dec(v_a_3240_);
                    crate::leanh::lean_dec(v_a_3238_);
                    crate::leanh::lean_del_object(v___x_3219_);
                    v___x_3248_ = crate::leanh::lean_box(0);
                    if v_isShared_3246_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3245_, 0, v___x_3248_);
                        v___x_3250_ = v___x_3245_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                        v___x_3250_ = v_reuseFailAlloc_3251_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3245_);
                    crate::leanh::lean_inc(v___y_3236_);
                    crate::leanh::lean_inc_ref(v___y_3235_);
                    crate::leanh::lean_inc(v___y_3234_);
                    crate::leanh::lean_inc_ref(v___y_3233_);
                    crate::leanh::lean_inc(v___y_3232_);
                    crate::leanh::lean_inc_ref(v___y_3231_);
                    crate::leanh::lean_inc(v___y_3230_);
                    crate::leanh::lean_inc_ref(v___y_3229_);
                    crate::leanh::lean_inc(v___y_3228_);
                    crate::leanh::lean_inc(v___y_3227_);
                    v___x_3252_ = lean_grind_mk_eq_proof(
                        v_a_3238_,
                        v_a_3240_,
                        v___y_3227_,
                        v___y_3228_,
                        v___y_3229_,
                        v___y_3230_,
                        v___y_3231_,
                        v___y_3232_,
                        v___y_3233_,
                        v___y_3234_,
                        v___y_3235_,
                        v___y_3236_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3252_) == 0 {
                        v_a_3253_ = crate::leanh::lean_ctor_get(v___x_3252_, 0);
                        v_isSharedCheck_3263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3252_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v___x_3255_ = v___x_3252_;
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3253_);
                            crate::leanh::lean_dec(v___x_3252_);
                            v___x_3255_ = crate::leanh::lean_box(0);
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3219_);
                        v_a_3264_ = crate::leanh::lean_ctor_get(v___x_3252_, 0);
                        v_isSharedCheck_3271_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3252_)) as u8;
                        if v_isSharedCheck_3271_ == 0 {
                            v___x_3266_ = v___x_3252_;
                            v_isShared_3267_ = v_isSharedCheck_3271_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3264_);
                            crate::leanh::lean_dec(v___x_3252_);
                            v___x_3266_ = crate::leanh::lean_box(0);
                            v_isShared_3267_ = v_isSharedCheck_3271_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_3250_;
            }
            7 => {
                if v_isShared_3220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3219_, 0, v_a_3253_);
                    v___x_3258_ = v___x_3219_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3253_);
                    v___x_3258_ = v_reuseFailAlloc_3262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3258_);
                    v___x_3260_ = v___x_3255_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
                    v___x_3260_ = v_reuseFailAlloc_3261_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3260_;
            }
            10 => {
                if v_isShared_3267_ == 0 {
                    v___x_3269_ = v___x_3266_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
                    v___x_3269_ = v_reuseFailAlloc_3270_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3269_;
            }
            12 => {
                if v_isShared_3276_ == 0 {
                    v___x_3278_ = v___x_3275_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3278_;
            }
            14 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3286_;
            }
            16 => {
                if v_isShared_3292_ == 0 {
                    v___x_3294_ = v___x_3291_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
                    v___x_3294_ = v_reuseFailAlloc_3295_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3294_;
            }
            18 => {
                if v_isShared_3300_ == 0 {
                    v___x_3302_ = v___x_3299_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
                    v___x_3302_ = v_reuseFailAlloc_3303_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3302_;
            }
            20 => {
                v___x_3315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
                v___x_3316_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3316_, 0, v___x_3314_);
                crate::leanh::lean_ctor_set(v___x_3316_, 1, v___x_3315_);
                crate::leanh::lean_inc(v_snd_3222_);
                v___x_3317_ = l_Lean_MessageData_ofExpr(v_snd_3222_);
                v___x_3318_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3318_, 0, v___x_3316_);
                crate::leanh::lean_ctor_set(v___x_3318_, 1, v___x_3317_);
                v___x_3319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
                v___x_3320_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3318_);
                crate::leanh::lean_ctor_set(v___x_3320_, 1, v___x_3319_);
                v___x_3321_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_3308_, v___x_3320_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
                if crate::leanh::lean_obj_tag(v___x_3321_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3321_, 1);
                    v___y_3227_ = v_a_3201_;
                    v___y_3228_ = v_a_3202_;
                    v___y_3229_ = v_a_3203_;
                    v___y_3230_ = v_a_3204_;
                    v___y_3231_ = v_a_3205_;
                    v___y_3232_ = v_a_3206_;
                    v___y_3233_ = v_a_3207_;
                    v___y_3234_ = v_a_3208_;
                    v___y_3235_ = v_a_3209_;
                    v___y_3236_ = v_a_3210_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3222_);
                    crate::leanh::lean_dec(v_fst_3221_);
                    crate::leanh::lean_del_object(v___x_3219_);
                    v_a_3322_ = crate::leanh::lean_ctor_get(v___x_3321_, 0);
                    v_isSharedCheck_3329_ = (!crate::leanh::lean_is_exclusive(v___x_3321_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3324_ = v___x_3321_;
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3322_);
                        crate::leanh::lean_dec(v___x_3321_);
                        v___x_3324_ = crate::leanh::lean_box(0);
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 21;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_3325_ == 0 {
                    v___x_3327_ = v___x_3324_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
                    v___x_3327_ = v_reuseFailAlloc_3328_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3327_;
            }
            23 => {
                return v___x_3335_;
            }
            24 => {
                if v_isShared_3341_ == 0 {
                    v___x_3343_ = v___x_3340_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed(
    mut v_lhs_u2080_3346_: *mut crate::leanh::LeanObject,
    mut v_rhs_u2080_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3359_ =
        l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(
            v_lhs_u2080_3346_,
            v_rhs_u2080_3347_,
            v_a_3348_,
            v_a_3349_,
            v_a_3350_,
            v_a_3351_,
            v_a_3352_,
            v_a_3353_,
            v_a_3354_,
            v_a_3355_,
            v_a_3356_,
            v_a_3357_,
        );
    crate::leanh::lean_dec(v_a_3357_);
    crate::leanh::lean_dec_ref(v_a_3356_);
    crate::leanh::lean_dec(v_a_3355_);
    crate::leanh::lean_dec_ref(v_a_3354_);
    crate::leanh::lean_dec(v_a_3353_);
    crate::leanh::lean_dec_ref(v_a_3352_);
    crate::leanh::lean_dec(v_a_3351_);
    crate::leanh::lean_dec_ref(v_a_3350_);
    crate::leanh::lean_dec(v_a_3349_);
    crate::leanh::lean_dec(v_a_3348_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(
    mut v_cls_3360_: *mut crate::leanh::LeanObject,
    mut v_msg_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3373_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_3360_, v_msg_3361_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(
    mut v_cls_3374_: *mut crate::leanh::LeanObject,
    mut v_msg_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_3374_, v_msg_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
    crate::leanh::lean_dec(v___y_3385_);
    crate::leanh::lean_dec_ref(v___y_3384_);
    crate::leanh::lean_dec(v___y_3383_);
    crate::leanh::lean_dec_ref(v___y_3382_);
    crate::leanh::lean_dec(v___y_3381_);
    crate::leanh::lean_dec_ref(v___y_3380_);
    crate::leanh::lean_dec(v___y_3379_);
    crate::leanh::lean_dec_ref(v___y_3378_);
    crate::leanh::lean_dec(v___y_3377_);
    crate::leanh::lean_dec(v___y_3376_);
    return v_res_3387_;
}
pub unsafe fn l_Lean_Meta_Grind_proveEq_x3f___lam__0(
    mut v_lhs_3388_: *mut crate::leanh::LeanObject,
    mut v_rhs_3389_: *mut crate::leanh::LeanObject,
    mut v_abstract_3390_: u8,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v_a_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v_a_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v_a_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_3388_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
                if crate::leanh::lean_obj_tag(v___x_3402_) == 0 {
                    v_a_3403_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    crate::leanh::lean_inc(v_a_3403_);
                    crate::leanh::lean_dec_ref_known(v___x_3402_, 1);
                    v___x_3404_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_3389_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
                    if crate::leanh::lean_obj_tag(v___x_3404_) == 0 {
                        v_a_3405_ = crate::leanh::lean_ctor_get(v___x_3404_, 0);
                        crate::leanh::lean_inc(v_a_3405_);
                        crate::leanh::lean_dec_ref_known(v___x_3404_, 1);
                        crate::leanh::lean_inc(v___y_3400_);
                        crate::leanh::lean_inc_ref(v___y_3399_);
                        crate::leanh::lean_inc(v___y_3398_);
                        crate::leanh::lean_inc_ref(v___y_3397_);
                        crate::leanh::lean_inc(v___y_3396_);
                        crate::leanh::lean_inc_ref(v___y_3395_);
                        crate::leanh::lean_inc(v___y_3394_);
                        crate::leanh::lean_inc_ref(v___y_3393_);
                        crate::leanh::lean_inc(v___y_3392_);
                        crate::leanh::lean_inc(v___y_3391_);
                        v___x_3406_ = lean_grind_process_new_facts(
                            v___y_3391_,
                            v___y_3392_,
                            v___y_3393_,
                            v___y_3394_,
                            v___y_3395_,
                            v___y_3396_,
                            v___y_3397_,
                            v___y_3398_,
                            v___y_3399_,
                            v___y_3400_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3406_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3406_, 1);
                            v___x_3407_ =
                                l_Lean_Meta_Grind_isEqv___redArg(v_a_3403_, v_a_3405_, v___y_3391_);
                            if crate::leanh::lean_obj_tag(v___x_3407_) == 0 {
                                v_a_3408_ = crate::leanh::lean_ctor_get(v___x_3407_, 0);
                                v_isSharedCheck_3436_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3407_)) as u8;
                                if v_isSharedCheck_3436_ == 0 {
                                    v___x_3410_ = v___x_3407_;
                                    v_isShared_3411_ = v_isSharedCheck_3436_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3408_);
                                    crate::leanh::lean_dec(v___x_3407_);
                                    v___x_3410_ = crate::leanh::lean_box(0);
                                    v_isShared_3411_ = v_isSharedCheck_3436_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3405_);
                                crate::leanh::lean_dec(v_a_3403_);
                                v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3407_, 0);
                                v_isSharedCheck_3444_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3407_)) as u8;
                                if v_isSharedCheck_3444_ == 0 {
                                    v___x_3439_ = v___x_3407_;
                                    v_isShared_3440_ = v_isSharedCheck_3444_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3437_);
                                    crate::leanh::lean_dec(v___x_3407_);
                                    v___x_3439_ = crate::leanh::lean_box(0);
                                    v_isShared_3440_ = v_isSharedCheck_3444_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3405_);
                            crate::leanh::lean_dec(v_a_3403_);
                            v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                            v_isSharedCheck_3452_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                            if v_isSharedCheck_3452_ == 0 {
                                v___x_3447_ = v___x_3406_;
                                v_isShared_3448_ = v_isSharedCheck_3452_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3445_);
                                crate::leanh::lean_dec(v___x_3406_);
                                v___x_3447_ = crate::leanh::lean_box(0);
                                v_isShared_3448_ = v_isSharedCheck_3452_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3403_);
                        v_a_3453_ = crate::leanh::lean_ctor_get(v___x_3404_, 0);
                        v_isSharedCheck_3460_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3404_)) as u8;
                        if v_isSharedCheck_3460_ == 0 {
                            v___x_3455_ = v___x_3404_;
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3453_);
                            crate::leanh::lean_dec(v___x_3404_);
                            v___x_3455_ = crate::leanh::lean_box(0);
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_3389_);
                    v_a_3461_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    v_isSharedCheck_3468_ = (!crate::leanh::lean_is_exclusive(v___x_3402_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3463_ = v___x_3402_;
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3461_);
                        crate::leanh::lean_dec(v___x_3402_);
                        v___x_3463_ = crate::leanh::lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3412_ = (crate::leanh::lean_unbox(v_a_3408_) as u8);
                crate::leanh::lean_dec(v_a_3408_);
                if v___x_3412_ == 0 {
                    if v_abstract_3390_ == 0 {
                        crate::leanh::lean_dec(v_a_3405_);
                        crate::leanh::lean_dec(v_a_3403_);
                        v___x_3413_ = crate::leanh::lean_box(0);
                        if v_isShared_3411_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3410_, 0, v___x_3413_);
                            v___x_3415_ = v___x_3410_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3416_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
                            v___x_3415_ = v_reuseFailAlloc_3416_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3410_);
                        v___x_3417_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_a_3403_, v_a_3405_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
                        return v___x_3417_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3410_);
                    crate::leanh::lean_inc(v___y_3400_);
                    crate::leanh::lean_inc_ref(v___y_3399_);
                    crate::leanh::lean_inc(v___y_3398_);
                    crate::leanh::lean_inc_ref(v___y_3397_);
                    crate::leanh::lean_inc(v___y_3396_);
                    crate::leanh::lean_inc_ref(v___y_3395_);
                    crate::leanh::lean_inc(v___y_3394_);
                    crate::leanh::lean_inc_ref(v___y_3393_);
                    crate::leanh::lean_inc(v___y_3392_);
                    crate::leanh::lean_inc(v___y_3391_);
                    v___x_3418_ = lean_grind_mk_eq_proof(
                        v_a_3403_,
                        v_a_3405_,
                        v___y_3391_,
                        v___y_3392_,
                        v___y_3393_,
                        v___y_3394_,
                        v___y_3395_,
                        v___y_3396_,
                        v___y_3397_,
                        v___y_3398_,
                        v___y_3399_,
                        v___y_3400_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3418_) == 0 {
                        v_a_3419_ = crate::leanh::lean_ctor_get(v___x_3418_, 0);
                        v_isSharedCheck_3427_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3418_)) as u8;
                        if v_isSharedCheck_3427_ == 0 {
                            v___x_3421_ = v___x_3418_;
                            v_isShared_3422_ = v_isSharedCheck_3427_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3419_);
                            crate::leanh::lean_dec(v___x_3418_);
                            v___x_3421_ = crate::leanh::lean_box(0);
                            v_isShared_3422_ = v_isSharedCheck_3427_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3428_ = crate::leanh::lean_ctor_get(v___x_3418_, 0);
                        v_isSharedCheck_3435_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3418_)) as u8;
                        if v_isSharedCheck_3435_ == 0 {
                            v___x_3430_ = v___x_3418_;
                            v_isShared_3431_ = v_isSharedCheck_3435_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3428_);
                            crate::leanh::lean_dec(v___x_3418_);
                            v___x_3430_ = crate::leanh::lean_box(0);
                            v_isShared_3431_ = v_isSharedCheck_3435_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3415_;
            }
            3 => {
                v___x_3423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3423_, 0, v_a_3419_);
                if v_isShared_3422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3421_, 0, v___x_3423_);
                    v___x_3425_ = v___x_3421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
                    v___x_3425_ = v_reuseFailAlloc_3426_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3425_;
            }
            5 => {
                if v_isShared_3431_ == 0 {
                    v___x_3433_ = v___x_3430_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
                    v___x_3433_ = v_reuseFailAlloc_3434_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3433_;
            }
            7 => {
                if v_isShared_3440_ == 0 {
                    v___x_3442_ = v___x_3439_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3442_;
            }
            9 => {
                if v_isShared_3448_ == 0 {
                    v___x_3450_ = v___x_3447_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
                    v___x_3450_ = v_reuseFailAlloc_3451_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3450_;
            }
            11 => {
                if v_isShared_3456_ == 0 {
                    v___x_3458_ = v___x_3455_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
                    v___x_3458_ = v_reuseFailAlloc_3459_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3458_;
            }
            13 => {
                if v_isShared_3464_ == 0 {
                    v___x_3466_ = v___x_3463_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
                    v___x_3466_ = v_reuseFailAlloc_3467_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed(
    mut v_lhs_3469_: *mut crate::leanh::LeanObject,
    mut v_rhs_3470_: *mut crate::leanh::LeanObject,
    mut v_abstract_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_abstract_boxed_3483_: u8 = 0;
    let mut v_res_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_abstract_boxed_3483_ = (crate::leanh::lean_unbox(v_abstract_3471_) as u8);
    v_res_3484_ = l_Lean_Meta_Grind_proveEq_x3f___lam__0(
        v_lhs_3469_,
        v_rhs_3470_,
        v_abstract_boxed_3483_,
        v___y_3472_,
        v___y_3473_,
        v___y_3474_,
        v___y_3475_,
        v___y_3476_,
        v___y_3477_,
        v___y_3478_,
        v___y_3479_,
        v___y_3480_,
        v___y_3481_,
    );
    crate::leanh::lean_dec(v___y_3481_);
    crate::leanh::lean_dec_ref(v___y_3480_);
    crate::leanh::lean_dec(v___y_3479_);
    crate::leanh::lean_dec_ref(v___y_3478_);
    crate::leanh::lean_dec(v___y_3477_);
    crate::leanh::lean_dec_ref(v___y_3476_);
    crate::leanh::lean_dec(v___y_3475_);
    crate::leanh::lean_dec_ref(v___y_3474_);
    crate::leanh::lean_dec(v___y_3473_);
    crate::leanh::lean_dec(v___y_3472_);
    return v_res_3484_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = l_Lean_Meta_Grind_proveEq_x3f___closed__0;
    v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_Meta_Grind_proveEq_x3f(
    mut v_lhs_3488_: *mut crate::leanh::LeanObject,
    mut v_rhs_3489_: *mut crate::leanh::LeanObject,
    mut v_abstract_3490_: u8,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3504_: u8 = 0;
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut v_a_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3547_: u8 = 0;
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut v_a_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_a_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut v___y_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3594_: u8 = 0;
    let mut v_a_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3598_: u8 = 0;
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_cls_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3502_ = crate::leanh::lean_ctor_get(v_a_3499_, 2);
                v_inheritedTraceOptions_3503_ = crate::leanh::lean_ctor_get(v_a_3499_, 13);
                v_hasTrace_3504_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3502_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_3505_ = crate::leanh::lean_box((v_abstract_3490_) as usize);
                crate::leanh::lean_inc_ref(v_rhs_3489_);
                crate::leanh::lean_inc_ref(v_lhs_3488_);
                v___f_3506_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed as *mut core::ffi::c_void,
                    14,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3506_, 0, v_lhs_3488_);
                crate::leanh::lean_closure_set(v___f_3506_, 1, v_rhs_3489_);
                crate::leanh::lean_closure_set(v___f_3506_, 2, v___x_3505_);
                if v_hasTrace_3504_ == 0 {
                    v___y_3570_ = v_a_3491_;
                    v___y_3571_ = v_a_3492_;
                    v___y_3572_ = v_a_3493_;
                    v___y_3573_ = v_a_3494_;
                    v___y_3574_ = v_a_3495_;
                    v___y_3575_ = v_a_3496_;
                    v___y_3576_ = v_a_3497_;
                    v___y_3577_ = v_a_3498_;
                    v___y_3578_ = v_a_3499_;
                    v___y_3579_ = v_a_3500_;
                    state = 12;
                    continue;
                } else {
                    v_cls_3603_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
                    v___x_3604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
                    v___x_3605_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3503_,
                        v_options_3502_,
                        v___x_3604_,
                    );
                    if v___x_3605_ == 0 {
                        v___y_3570_ = v_a_3491_;
                        v___y_3571_ = v_a_3492_;
                        v___y_3572_ = v_a_3493_;
                        v___y_3573_ = v_a_3494_;
                        v___y_3574_ = v_a_3495_;
                        v___y_3575_ = v_a_3496_;
                        v___y_3576_ = v_a_3497_;
                        v___y_3577_ = v_a_3498_;
                        v___y_3578_ = v_a_3499_;
                        v___y_3579_ = v_a_3500_;
                        state = 12;
                        continue;
                    } else {
                        v___x_3606_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_proveEq_x3f___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_proveEq_x3f___closed__1_once),
                            _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1,
                        );
                        crate::leanh::lean_inc_ref(v_lhs_3488_);
                        v___x_3607_ = l_Lean_MessageData_ofExpr(v_lhs_3488_);
                        v___x_3608_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3608_, 0, v___x_3606_);
                        crate::leanh::lean_ctor_set(v___x_3608_, 1, v___x_3607_);
                        v___x_3609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
                        v___x_3610_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3608_);
                        crate::leanh::lean_ctor_set(v___x_3610_, 1, v___x_3609_);
                        crate::leanh::lean_inc_ref(v_rhs_3489_);
                        v___x_3611_ = l_Lean_MessageData_ofExpr(v_rhs_3489_);
                        v___x_3612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                        crate::leanh::lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                        v___x_3613_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
                        v___x_3614_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3614_, 0, v___x_3612_);
                        crate::leanh::lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                        v___x_3615_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_3603_, v___x_3614_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
                        if crate::leanh::lean_obj_tag(v___x_3615_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3615_, 1);
                            v___y_3570_ = v_a_3491_;
                            v___y_3571_ = v_a_3492_;
                            v___y_3572_ = v_a_3493_;
                            v___y_3573_ = v_a_3494_;
                            v___y_3574_ = v_a_3495_;
                            v___y_3575_ = v_a_3496_;
                            v___y_3576_ = v_a_3497_;
                            v___y_3577_ = v_a_3498_;
                            v___y_3578_ = v_a_3499_;
                            v___y_3579_ = v_a_3500_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_3506_);
                            crate::leanh::lean_dec_ref(v_rhs_3489_);
                            crate::leanh::lean_dec_ref(v_lhs_3488_);
                            v_a_3616_ = crate::leanh::lean_ctor_get(v___x_3615_, 0);
                            v_isSharedCheck_3623_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3615_)) as u8;
                            if v_isSharedCheck_3623_ == 0 {
                                v___x_3618_ = v___x_3615_;
                                v_isShared_3619_ = v_isSharedCheck_3623_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3616_);
                                crate::leanh::lean_dec(v___x_3615_);
                                v___x_3618_ = crate::leanh::lean_box(0);
                                v_isShared_3619_ = v_isSharedCheck_3623_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3518_) == 0 {
                    v_a_3519_ = crate::leanh::lean_ctor_get(v___y_3518_, 0);
                    crate::leanh::lean_inc(v_a_3519_);
                    crate::leanh::lean_dec_ref_known(v___y_3518_, 1);
                    v___x_3520_ = (crate::leanh::lean_unbox(v_a_3519_) as u8);
                    crate::leanh::lean_dec(v_a_3519_);
                    if v___x_3520_ == 0 {
                        crate::leanh::lean_dec_ref(v_rhs_3489_);
                        crate::leanh::lean_dec_ref(v_lhs_3488_);
                        v___x_3521_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(
                            v___f_3506_,
                            v___y_3516_,
                            v___y_3513_,
                            v___y_3511_,
                            v___y_3510_,
                            v___y_3515_,
                            v___y_3509_,
                            v___y_3517_,
                            v___y_3508_,
                            v___y_3512_,
                            v___y_3514_,
                        );
                        return v___x_3521_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_3506_);
                        v___x_3522_ =
                            l_Lean_Meta_Grind_isEqv___redArg(v_lhs_3488_, v_rhs_3489_, v___y_3516_);
                        if crate::leanh::lean_obj_tag(v___x_3522_) == 0 {
                            v_a_3523_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                            v_isSharedCheck_3552_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3522_)) as u8;
                            if v_isSharedCheck_3552_ == 0 {
                                v___x_3525_ = v___x_3522_;
                                v_isShared_3526_ = v_isSharedCheck_3552_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3523_);
                                crate::leanh::lean_dec(v___x_3522_);
                                v___x_3525_ = crate::leanh::lean_box(0);
                                v_isShared_3526_ = v_isSharedCheck_3552_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_rhs_3489_);
                            crate::leanh::lean_dec_ref(v_lhs_3488_);
                            v_a_3553_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                            v_isSharedCheck_3560_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3522_)) as u8;
                            if v_isSharedCheck_3560_ == 0 {
                                v___x_3555_ = v___x_3522_;
                                v_isShared_3556_ = v_isSharedCheck_3560_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3553_);
                                crate::leanh::lean_dec(v___x_3522_);
                                v___x_3555_ = crate::leanh::lean_box(0);
                                v_isShared_3556_ = v_isSharedCheck_3560_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3506_);
                    crate::leanh::lean_dec_ref(v_rhs_3489_);
                    crate::leanh::lean_dec_ref(v_lhs_3488_);
                    v_a_3561_ = crate::leanh::lean_ctor_get(v___y_3518_, 0);
                    v_isSharedCheck_3568_ = (!crate::leanh::lean_is_exclusive(v___y_3518_)) as u8;
                    if v_isSharedCheck_3568_ == 0 {
                        v___x_3563_ = v___y_3518_;
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3561_);
                        crate::leanh::lean_dec(v___y_3518_);
                        v___x_3563_ = crate::leanh::lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3527_ = (crate::leanh::lean_unbox(v_a_3523_) as u8);
                crate::leanh::lean_dec(v_a_3523_);
                if v___x_3527_ == 0 {
                    if v_abstract_3490_ == 0 {
                        crate::leanh::lean_dec_ref(v_rhs_3489_);
                        crate::leanh::lean_dec_ref(v_lhs_3488_);
                        v___x_3528_ = crate::leanh::lean_box(0);
                        if v_isShared_3526_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3525_, 0, v___x_3528_);
                            v___x_3530_ = v___x_3525_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3531_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
                            v___x_3530_ = v_reuseFailAlloc_3531_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3525_);
                        v___x_3532_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed as *mut core::ffi::c_void, 13, 2);
                        crate::leanh::lean_closure_set(v___x_3532_, 0, v_lhs_3488_);
                        crate::leanh::lean_closure_set(v___x_3532_, 1, v_rhs_3489_);
                        v___x_3533_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(
                            v___x_3532_,
                            v___y_3516_,
                            v___y_3513_,
                            v___y_3511_,
                            v___y_3510_,
                            v___y_3515_,
                            v___y_3509_,
                            v___y_3517_,
                            v___y_3508_,
                            v___y_3512_,
                            v___y_3514_,
                        );
                        return v___x_3533_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3525_);
                    crate::leanh::lean_inc(v___y_3514_);
                    crate::leanh::lean_inc_ref(v___y_3512_);
                    crate::leanh::lean_inc(v___y_3508_);
                    crate::leanh::lean_inc_ref(v___y_3517_);
                    crate::leanh::lean_inc(v___y_3509_);
                    crate::leanh::lean_inc_ref(v___y_3515_);
                    crate::leanh::lean_inc(v___y_3510_);
                    crate::leanh::lean_inc_ref(v___y_3511_);
                    crate::leanh::lean_inc(v___y_3513_);
                    crate::leanh::lean_inc(v___y_3516_);
                    v___x_3534_ = lean_grind_mk_eq_proof(
                        v_lhs_3488_,
                        v_rhs_3489_,
                        v___y_3516_,
                        v___y_3513_,
                        v___y_3511_,
                        v___y_3510_,
                        v___y_3515_,
                        v___y_3509_,
                        v___y_3517_,
                        v___y_3508_,
                        v___y_3512_,
                        v___y_3514_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3534_) == 0 {
                        v_a_3535_ = crate::leanh::lean_ctor_get(v___x_3534_, 0);
                        v_isSharedCheck_3543_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3534_)) as u8;
                        if v_isSharedCheck_3543_ == 0 {
                            v___x_3537_ = v___x_3534_;
                            v_isShared_3538_ = v_isSharedCheck_3543_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3535_);
                            crate::leanh::lean_dec(v___x_3534_);
                            v___x_3537_ = crate::leanh::lean_box(0);
                            v_isShared_3538_ = v_isSharedCheck_3543_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3544_ = crate::leanh::lean_ctor_get(v___x_3534_, 0);
                        v_isSharedCheck_3551_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3534_)) as u8;
                        if v_isSharedCheck_3551_ == 0 {
                            v___x_3546_ = v___x_3534_;
                            v_isShared_3547_ = v_isSharedCheck_3551_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3544_);
                            crate::leanh::lean_dec(v___x_3534_);
                            v___x_3546_ = crate::leanh::lean_box(0);
                            v_isShared_3547_ = v_isSharedCheck_3551_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3530_;
            }
            4 => {
                v___x_3539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3539_, 0, v_a_3535_);
                if v_isShared_3538_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3537_, 0, v___x_3539_);
                    v___x_3541_ = v___x_3537_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
                    v___x_3541_ = v_reuseFailAlloc_3542_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3541_;
            }
            6 => {
                if v_isShared_3547_ == 0 {
                    v___x_3549_ = v___x_3546_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
                    v___x_3549_ = v_reuseFailAlloc_3550_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3549_;
            }
            8 => {
                if v_isShared_3556_ == 0 {
                    v___x_3558_ = v___x_3555_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3558_;
            }
            10 => {
                if v_isShared_3564_ == 0 {
                    v___x_3566_ = v___x_3563_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
                    v___x_3566_ = v_reuseFailAlloc_3567_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3566_;
            }
            12 => {
                crate::leanh::lean_inc_ref(v_rhs_3489_);
                crate::leanh::lean_inc_ref(v_lhs_3488_);
                v___x_3580_ = l_Lean_Meta_Grind_hasSameType(
                    v_lhs_3488_,
                    v_rhs_3489_,
                    v___y_3576_,
                    v___y_3577_,
                    v___y_3578_,
                    v___y_3579_,
                );
                if crate::leanh::lean_obj_tag(v___x_3580_) == 0 {
                    v_a_3581_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                    v_isSharedCheck_3594_ = (!crate::leanh::lean_is_exclusive(v___x_3580_)) as u8;
                    if v_isSharedCheck_3594_ == 0 {
                        v___x_3583_ = v___x_3580_;
                        v_isShared_3584_ = v_isSharedCheck_3594_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3581_);
                        crate::leanh::lean_dec(v___x_3580_);
                        v___x_3583_ = crate::leanh::lean_box(0);
                        v_isShared_3584_ = v_isSharedCheck_3594_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3506_);
                    crate::leanh::lean_dec_ref(v_rhs_3489_);
                    crate::leanh::lean_dec_ref(v_lhs_3488_);
                    v_a_3595_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                    v_isSharedCheck_3602_ = (!crate::leanh::lean_is_exclusive(v___x_3580_)) as u8;
                    if v_isSharedCheck_3602_ == 0 {
                        v___x_3597_ = v___x_3580_;
                        v_isShared_3598_ = v_isSharedCheck_3602_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3595_);
                        crate::leanh::lean_dec(v___x_3580_);
                        v___x_3597_ = crate::leanh::lean_box(0);
                        v_isShared_3598_ = v_isSharedCheck_3602_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                v___x_3585_ = (crate::leanh::lean_unbox(v_a_3581_) as u8);
                crate::leanh::lean_dec(v_a_3581_);
                if v___x_3585_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_3506_);
                    crate::leanh::lean_dec_ref(v_rhs_3489_);
                    crate::leanh::lean_dec_ref(v_lhs_3488_);
                    v___x_3586_ = crate::leanh::lean_box(0);
                    if v_isShared_3584_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3583_, 0, v___x_3586_);
                        v___x_3588_ = v___x_3583_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
                        v___x_3588_ = v_reuseFailAlloc_3589_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3583_);
                    v___x_3590_ =
                        l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_3488_, v___y_3570_);
                    if crate::leanh::lean_obj_tag(v___x_3590_) == 0 {
                        v_a_3591_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                        crate::leanh::lean_inc(v_a_3591_);
                        v___x_3592_ = (crate::leanh::lean_unbox(v_a_3591_) as u8);
                        crate::leanh::lean_dec(v_a_3591_);
                        if v___x_3592_ == 0 {
                            v___y_3508_ = v___y_3577_;
                            v___y_3509_ = v___y_3575_;
                            v___y_3510_ = v___y_3573_;
                            v___y_3511_ = v___y_3572_;
                            v___y_3512_ = v___y_3578_;
                            v___y_3513_ = v___y_3571_;
                            v___y_3514_ = v___y_3579_;
                            v___y_3515_ = v___y_3574_;
                            v___y_3516_ = v___y_3570_;
                            v___y_3517_ = v___y_3576_;
                            v___y_3518_ = v___x_3590_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3590_, 1);
                            v___x_3593_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(
                                v_rhs_3489_,
                                v___y_3570_,
                            );
                            v___y_3508_ = v___y_3577_;
                            v___y_3509_ = v___y_3575_;
                            v___y_3510_ = v___y_3573_;
                            v___y_3511_ = v___y_3572_;
                            v___y_3512_ = v___y_3578_;
                            v___y_3513_ = v___y_3571_;
                            v___y_3514_ = v___y_3579_;
                            v___y_3515_ = v___y_3574_;
                            v___y_3516_ = v___y_3570_;
                            v___y_3517_ = v___y_3576_;
                            v___y_3518_ = v___x_3593_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_3508_ = v___y_3577_;
                        v___y_3509_ = v___y_3575_;
                        v___y_3510_ = v___y_3573_;
                        v___y_3511_ = v___y_3572_;
                        v___y_3512_ = v___y_3578_;
                        v___y_3513_ = v___y_3571_;
                        v___y_3514_ = v___y_3579_;
                        v___y_3515_ = v___y_3574_;
                        v___y_3516_ = v___y_3570_;
                        v___y_3517_ = v___y_3576_;
                        v___y_3518_ = v___x_3590_;
                        state = 1;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_3588_;
            }
            15 => {
                if v_isShared_3598_ == 0 {
                    v___x_3600_ = v___x_3597_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
                    v___x_3600_ = v_reuseFailAlloc_3601_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3600_;
            }
            17 => {
                if v_isShared_3619_ == 0 {
                    v___x_3621_ = v___x_3618_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
                    v___x_3621_ = v_reuseFailAlloc_3622_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_proveEq_x3f___boxed(
    mut v_lhs_3624_: *mut crate::leanh::LeanObject,
    mut v_rhs_3625_: *mut crate::leanh::LeanObject,
    mut v_abstract_3626_: *mut crate::leanh::LeanObject,
    mut v_a_3627_: *mut crate::leanh::LeanObject,
    mut v_a_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
    mut v_a_3635_: *mut crate::leanh::LeanObject,
    mut v_a_3636_: *mut crate::leanh::LeanObject,
    mut v_a_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_abstract_boxed_3638_: u8 = 0;
    let mut v_res_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_abstract_boxed_3638_ = (crate::leanh::lean_unbox(v_abstract_3626_) as u8);
    v_res_3639_ = l_Lean_Meta_Grind_proveEq_x3f(
        v_lhs_3624_,
        v_rhs_3625_,
        v_abstract_boxed_3638_,
        v_a_3627_,
        v_a_3628_,
        v_a_3629_,
        v_a_3630_,
        v_a_3631_,
        v_a_3632_,
        v_a_3633_,
        v_a_3634_,
        v_a_3635_,
        v_a_3636_,
    );
    crate::leanh::lean_dec(v_a_3636_);
    crate::leanh::lean_dec_ref(v_a_3635_);
    crate::leanh::lean_dec(v_a_3634_);
    crate::leanh::lean_dec_ref(v_a_3633_);
    crate::leanh::lean_dec(v_a_3632_);
    crate::leanh::lean_dec_ref(v_a_3631_);
    crate::leanh::lean_dec(v_a_3630_);
    crate::leanh::lean_dec_ref(v_a_3629_);
    crate::leanh::lean_dec(v_a_3628_);
    crate::leanh::lean_dec(v_a_3627_);
    return v_res_3639_;
}
pub unsafe fn l_Lean_Meta_Grind_proveHEq_x3f___lam__0(
    mut v_lhs_3640_: *mut crate::leanh::LeanObject,
    mut v_rhs_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
    mut v___y_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3662_: u8 = 0;
    let mut v___x_3663_: u8 = 0;
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_a_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_a_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_a_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3653_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_3640_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
                if crate::leanh::lean_obj_tag(v___x_3653_) == 0 {
                    v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3653_, 0);
                    crate::leanh::lean_inc(v_a_3654_);
                    crate::leanh::lean_dec_ref_known(v___x_3653_, 1);
                    v___x_3655_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
                    if crate::leanh::lean_obj_tag(v___x_3655_) == 0 {
                        v_a_3656_ = crate::leanh::lean_ctor_get(v___x_3655_, 0);
                        crate::leanh::lean_inc(v_a_3656_);
                        crate::leanh::lean_dec_ref_known(v___x_3655_, 1);
                        crate::leanh::lean_inc(v___y_3651_);
                        crate::leanh::lean_inc_ref(v___y_3650_);
                        crate::leanh::lean_inc(v___y_3649_);
                        crate::leanh::lean_inc_ref(v___y_3648_);
                        crate::leanh::lean_inc(v___y_3647_);
                        crate::leanh::lean_inc_ref(v___y_3646_);
                        crate::leanh::lean_inc(v___y_3645_);
                        crate::leanh::lean_inc_ref(v___y_3644_);
                        crate::leanh::lean_inc(v___y_3643_);
                        crate::leanh::lean_inc(v___y_3642_);
                        v___x_3657_ = lean_grind_process_new_facts(
                            v___y_3642_,
                            v___y_3643_,
                            v___y_3644_,
                            v___y_3645_,
                            v___y_3646_,
                            v___y_3647_,
                            v___y_3648_,
                            v___y_3649_,
                            v___y_3650_,
                            v___y_3651_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3657_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3657_, 1);
                            v___x_3658_ =
                                l_Lean_Meta_Grind_isEqv___redArg(v_a_3654_, v_a_3656_, v___y_3642_);
                            if crate::leanh::lean_obj_tag(v___x_3658_) == 0 {
                                v_a_3659_ = crate::leanh::lean_ctor_get(v___x_3658_, 0);
                                v_isSharedCheck_3686_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3658_)) as u8;
                                if v_isSharedCheck_3686_ == 0 {
                                    v___x_3661_ = v___x_3658_;
                                    v_isShared_3662_ = v_isSharedCheck_3686_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3659_);
                                    crate::leanh::lean_dec(v___x_3658_);
                                    v___x_3661_ = crate::leanh::lean_box(0);
                                    v_isShared_3662_ = v_isSharedCheck_3686_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3656_);
                                crate::leanh::lean_dec(v_a_3654_);
                                v_a_3687_ = crate::leanh::lean_ctor_get(v___x_3658_, 0);
                                v_isSharedCheck_3694_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3658_)) as u8;
                                if v_isSharedCheck_3694_ == 0 {
                                    v___x_3689_ = v___x_3658_;
                                    v_isShared_3690_ = v_isSharedCheck_3694_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3687_);
                                    crate::leanh::lean_dec(v___x_3658_);
                                    v___x_3689_ = crate::leanh::lean_box(0);
                                    v_isShared_3690_ = v_isSharedCheck_3694_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3656_);
                            crate::leanh::lean_dec(v_a_3654_);
                            v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3657_, 0);
                            v_isSharedCheck_3702_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3657_)) as u8;
                            if v_isSharedCheck_3702_ == 0 {
                                v___x_3697_ = v___x_3657_;
                                v_isShared_3698_ = v_isSharedCheck_3702_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3695_);
                                crate::leanh::lean_dec(v___x_3657_);
                                v___x_3697_ = crate::leanh::lean_box(0);
                                v_isShared_3698_ = v_isSharedCheck_3702_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3654_);
                        v_a_3703_ = crate::leanh::lean_ctor_get(v___x_3655_, 0);
                        v_isSharedCheck_3710_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3655_)) as u8;
                        if v_isSharedCheck_3710_ == 0 {
                            v___x_3705_ = v___x_3655_;
                            v_isShared_3706_ = v_isSharedCheck_3710_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3703_);
                            crate::leanh::lean_dec(v___x_3655_);
                            v___x_3705_ = crate::leanh::lean_box(0);
                            v_isShared_3706_ = v_isSharedCheck_3710_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_3641_);
                    v_a_3711_ = crate::leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3718_ = (!crate::leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3718_ == 0 {
                        v___x_3713_ = v___x_3653_;
                        v_isShared_3714_ = v_isSharedCheck_3718_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3711_);
                        crate::leanh::lean_dec(v___x_3653_);
                        v___x_3713_ = crate::leanh::lean_box(0);
                        v_isShared_3714_ = v_isSharedCheck_3718_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3663_ = (crate::leanh::lean_unbox(v_a_3659_) as u8);
                crate::leanh::lean_dec(v_a_3659_);
                if v___x_3663_ == 0 {
                    crate::leanh::lean_dec(v_a_3656_);
                    crate::leanh::lean_dec(v_a_3654_);
                    v___x_3664_ = crate::leanh::lean_box(0);
                    if v_isShared_3662_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3661_, 0, v___x_3664_);
                        v___x_3666_ = v___x_3661_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                        v___x_3666_ = v_reuseFailAlloc_3667_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3661_);
                    crate::leanh::lean_inc(v___y_3651_);
                    crate::leanh::lean_inc_ref(v___y_3650_);
                    crate::leanh::lean_inc(v___y_3649_);
                    crate::leanh::lean_inc_ref(v___y_3648_);
                    crate::leanh::lean_inc(v___y_3647_);
                    crate::leanh::lean_inc_ref(v___y_3646_);
                    crate::leanh::lean_inc(v___y_3645_);
                    crate::leanh::lean_inc_ref(v___y_3644_);
                    crate::leanh::lean_inc(v___y_3643_);
                    crate::leanh::lean_inc(v___y_3642_);
                    v___x_3668_ = lean_grind_mk_heq_proof(
                        v_a_3654_,
                        v_a_3656_,
                        v___y_3642_,
                        v___y_3643_,
                        v___y_3644_,
                        v___y_3645_,
                        v___y_3646_,
                        v___y_3647_,
                        v___y_3648_,
                        v___y_3649_,
                        v___y_3650_,
                        v___y_3651_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3668_) == 0 {
                        v_a_3669_ = crate::leanh::lean_ctor_get(v___x_3668_, 0);
                        v_isSharedCheck_3677_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3668_)) as u8;
                        if v_isSharedCheck_3677_ == 0 {
                            v___x_3671_ = v___x_3668_;
                            v_isShared_3672_ = v_isSharedCheck_3677_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3669_);
                            crate::leanh::lean_dec(v___x_3668_);
                            v___x_3671_ = crate::leanh::lean_box(0);
                            v_isShared_3672_ = v_isSharedCheck_3677_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3678_ = crate::leanh::lean_ctor_get(v___x_3668_, 0);
                        v_isSharedCheck_3685_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3668_)) as u8;
                        if v_isSharedCheck_3685_ == 0 {
                            v___x_3680_ = v___x_3668_;
                            v_isShared_3681_ = v_isSharedCheck_3685_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3678_);
                            crate::leanh::lean_dec(v___x_3668_);
                            v___x_3680_ = crate::leanh::lean_box(0);
                            v_isShared_3681_ = v_isSharedCheck_3685_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3666_;
            }
            3 => {
                v___x_3673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3673_, 0, v_a_3669_);
                if v_isShared_3672_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3671_, 0, v___x_3673_);
                    v___x_3675_ = v___x_3671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
                    v___x_3675_ = v_reuseFailAlloc_3676_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3675_;
            }
            5 => {
                if v_isShared_3681_ == 0 {
                    v___x_3683_ = v___x_3680_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3683_;
            }
            7 => {
                if v_isShared_3690_ == 0 {
                    v___x_3692_ = v___x_3689_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3692_;
            }
            9 => {
                if v_isShared_3698_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3700_;
            }
            11 => {
                if v_isShared_3706_ == 0 {
                    v___x_3708_ = v___x_3705_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3708_;
            }
            13 => {
                if v_isShared_3714_ == 0 {
                    v___x_3716_ = v___x_3713_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed(
    mut v_lhs_3719_: *mut crate::leanh::LeanObject,
    mut v_rhs_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
    mut v___y_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_Lean_Meta_Grind_proveHEq_x3f___lam__0(
        v_lhs_3719_,
        v_rhs_3720_,
        v___y_3721_,
        v___y_3722_,
        v___y_3723_,
        v___y_3724_,
        v___y_3725_,
        v___y_3726_,
        v___y_3727_,
        v___y_3728_,
        v___y_3729_,
        v___y_3730_,
    );
    crate::leanh::lean_dec(v___y_3730_);
    crate::leanh::lean_dec_ref(v___y_3729_);
    crate::leanh::lean_dec(v___y_3728_);
    crate::leanh::lean_dec_ref(v___y_3727_);
    crate::leanh::lean_dec(v___y_3726_);
    crate::leanh::lean_dec_ref(v___y_3725_);
    crate::leanh::lean_dec(v___y_3724_);
    crate::leanh::lean_dec_ref(v___y_3723_);
    crate::leanh::lean_dec(v___y_3722_);
    crate::leanh::lean_dec(v___y_3721_);
    return v_res_3732_;
}
pub unsafe fn l_Lean_Meta_Grind_proveHEq_x3f(
    mut v_lhs_3733_: *mut crate::leanh::LeanObject,
    mut v_rhs_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
    mut v_a_3744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut v_a_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3775_: u8 = 0;
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_isSharedCheck_3780_: u8 = 0;
    let mut v_a_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3784_: u8 = 0;
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3788_: u8 = 0;
    let mut v_a_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: u8 = 0;
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_rhs_3734_);
                crate::leanh::lean_inc_ref(v_lhs_3733_);
                v___f_3746_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3746_, 0, v_lhs_3733_);
                crate::leanh::lean_closure_set(v___f_3746_, 1, v_rhs_3734_);
                v___x_3797_ =
                    l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_3733_, v_a_3735_);
                if crate::leanh::lean_obj_tag(v___x_3797_) == 0 {
                    v_a_3798_ = crate::leanh::lean_ctor_get(v___x_3797_, 0);
                    crate::leanh::lean_inc(v_a_3798_);
                    v___x_3799_ = (crate::leanh::lean_unbox(v_a_3798_) as u8);
                    crate::leanh::lean_dec(v_a_3798_);
                    if v___x_3799_ == 0 {
                        v___y_3748_ = v___x_3797_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3797_, 1);
                        v___x_3800_ =
                            l_Lean_Meta_Grind_alreadyInternalized___redArg(v_rhs_3734_, v_a_3735_);
                        v___y_3748_ = v___x_3800_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3748_ = v___x_3797_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3748_) == 0 {
                    v_a_3749_ = crate::leanh::lean_ctor_get(v___y_3748_, 0);
                    crate::leanh::lean_inc(v_a_3749_);
                    crate::leanh::lean_dec_ref_known(v___y_3748_, 1);
                    v___x_3750_ = (crate::leanh::lean_unbox(v_a_3749_) as u8);
                    crate::leanh::lean_dec(v_a_3749_);
                    if v___x_3750_ == 0 {
                        crate::leanh::lean_dec_ref(v_rhs_3734_);
                        crate::leanh::lean_dec_ref(v_lhs_3733_);
                        v___x_3751_ = l_Lean_Meta_Grind_withoutModifyingState___redArg(
                            v___f_3746_,
                            v_a_3735_,
                            v_a_3736_,
                            v_a_3737_,
                            v_a_3738_,
                            v_a_3739_,
                            v_a_3740_,
                            v_a_3741_,
                            v_a_3742_,
                            v_a_3743_,
                            v_a_3744_,
                        );
                        return v___x_3751_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_3746_);
                        v___x_3752_ =
                            l_Lean_Meta_Grind_isEqv___redArg(v_lhs_3733_, v_rhs_3734_, v_a_3735_);
                        if crate::leanh::lean_obj_tag(v___x_3752_) == 0 {
                            v_a_3753_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
                            v_isSharedCheck_3780_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3752_)) as u8;
                            if v_isSharedCheck_3780_ == 0 {
                                v___x_3755_ = v___x_3752_;
                                v_isShared_3756_ = v_isSharedCheck_3780_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3753_);
                                crate::leanh::lean_dec(v___x_3752_);
                                v___x_3755_ = crate::leanh::lean_box(0);
                                v_isShared_3756_ = v_isSharedCheck_3780_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_rhs_3734_);
                            crate::leanh::lean_dec_ref(v_lhs_3733_);
                            v_a_3781_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
                            v_isSharedCheck_3788_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3752_)) as u8;
                            if v_isSharedCheck_3788_ == 0 {
                                v___x_3783_ = v___x_3752_;
                                v_isShared_3784_ = v_isSharedCheck_3788_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3781_);
                                crate::leanh::lean_dec(v___x_3752_);
                                v___x_3783_ = crate::leanh::lean_box(0);
                                v_isShared_3784_ = v_isSharedCheck_3788_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3746_);
                    crate::leanh::lean_dec_ref(v_rhs_3734_);
                    crate::leanh::lean_dec_ref(v_lhs_3733_);
                    v_a_3789_ = crate::leanh::lean_ctor_get(v___y_3748_, 0);
                    v_isSharedCheck_3796_ = (!crate::leanh::lean_is_exclusive(v___y_3748_)) as u8;
                    if v_isSharedCheck_3796_ == 0 {
                        v___x_3791_ = v___y_3748_;
                        v_isShared_3792_ = v_isSharedCheck_3796_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3789_);
                        crate::leanh::lean_dec(v___y_3748_);
                        v___x_3791_ = crate::leanh::lean_box(0);
                        v_isShared_3792_ = v_isSharedCheck_3796_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3757_ = (crate::leanh::lean_unbox(v_a_3753_) as u8);
                crate::leanh::lean_dec(v_a_3753_);
                if v___x_3757_ == 0 {
                    crate::leanh::lean_dec_ref(v_rhs_3734_);
                    crate::leanh::lean_dec_ref(v_lhs_3733_);
                    v___x_3758_ = crate::leanh::lean_box(0);
                    if v_isShared_3756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3758_);
                        v___x_3760_ = v___x_3755_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3761_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
                        v___x_3760_ = v_reuseFailAlloc_3761_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3755_);
                    crate::leanh::lean_inc(v_a_3744_);
                    crate::leanh::lean_inc_ref(v_a_3743_);
                    crate::leanh::lean_inc(v_a_3742_);
                    crate::leanh::lean_inc_ref(v_a_3741_);
                    crate::leanh::lean_inc(v_a_3740_);
                    crate::leanh::lean_inc_ref(v_a_3739_);
                    crate::leanh::lean_inc(v_a_3738_);
                    crate::leanh::lean_inc_ref(v_a_3737_);
                    crate::leanh::lean_inc(v_a_3736_);
                    crate::leanh::lean_inc(v_a_3735_);
                    v___x_3762_ = lean_grind_mk_heq_proof(
                        v_lhs_3733_,
                        v_rhs_3734_,
                        v_a_3735_,
                        v_a_3736_,
                        v_a_3737_,
                        v_a_3738_,
                        v_a_3739_,
                        v_a_3740_,
                        v_a_3741_,
                        v_a_3742_,
                        v_a_3743_,
                        v_a_3744_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3762_) == 0 {
                        v_a_3763_ = crate::leanh::lean_ctor_get(v___x_3762_, 0);
                        v_isSharedCheck_3771_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3762_)) as u8;
                        if v_isSharedCheck_3771_ == 0 {
                            v___x_3765_ = v___x_3762_;
                            v_isShared_3766_ = v_isSharedCheck_3771_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3763_);
                            crate::leanh::lean_dec(v___x_3762_);
                            v___x_3765_ = crate::leanh::lean_box(0);
                            v_isShared_3766_ = v_isSharedCheck_3771_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3772_ = crate::leanh::lean_ctor_get(v___x_3762_, 0);
                        v_isSharedCheck_3779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3762_)) as u8;
                        if v_isSharedCheck_3779_ == 0 {
                            v___x_3774_ = v___x_3762_;
                            v_isShared_3775_ = v_isSharedCheck_3779_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3772_);
                            crate::leanh::lean_dec(v___x_3762_);
                            v___x_3774_ = crate::leanh::lean_box(0);
                            v_isShared_3775_ = v_isSharedCheck_3779_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3760_;
            }
            4 => {
                v___x_3767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3767_, 0, v_a_3763_);
                if v_isShared_3766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3765_, 0, v___x_3767_);
                    v___x_3769_ = v___x_3765_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
                    v___x_3769_ = v_reuseFailAlloc_3770_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3769_;
            }
            6 => {
                if v_isShared_3775_ == 0 {
                    v___x_3777_ = v___x_3774_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
                    v___x_3777_ = v_reuseFailAlloc_3778_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3777_;
            }
            8 => {
                if v_isShared_3784_ == 0 {
                    v___x_3786_ = v___x_3783_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
                    v___x_3786_ = v_reuseFailAlloc_3787_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3786_;
            }
            10 => {
                if v_isShared_3792_ == 0 {
                    v___x_3794_ = v___x_3791_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
                    v___x_3794_ = v_reuseFailAlloc_3795_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_proveHEq_x3f___boxed(
    mut v_lhs_3801_: *mut crate::leanh::LeanObject,
    mut v_rhs_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_a_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
    mut v_a_3807_: *mut crate::leanh::LeanObject,
    mut v_a_3808_: *mut crate::leanh::LeanObject,
    mut v_a_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3814_ = l_Lean_Meta_Grind_proveHEq_x3f(
        v_lhs_3801_,
        v_rhs_3802_,
        v_a_3803_,
        v_a_3804_,
        v_a_3805_,
        v_a_3806_,
        v_a_3807_,
        v_a_3808_,
        v_a_3809_,
        v_a_3810_,
        v_a_3811_,
        v_a_3812_,
    );
    crate::leanh::lean_dec(v_a_3812_);
    crate::leanh::lean_dec_ref(v_a_3811_);
    crate::leanh::lean_dec(v_a_3810_);
    crate::leanh::lean_dec_ref(v_a_3809_);
    crate::leanh::lean_dec(v_a_3808_);
    crate::leanh::lean_dec_ref(v_a_3807_);
    crate::leanh::lean_dec(v_a_3806_);
    crate::leanh::lean_dec_ref(v_a_3805_);
    crate::leanh::lean_dec(v_a_3804_);
    crate::leanh::lean_dec(v_a_3803_);
    return v_res_3814_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_ProveEq(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_ProveEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
}
