// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ProveEq
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Util Lean.Meta.Tactic.Grind.Simp
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::{
    lean_grind_internalize, lean_grind_mk_eq_proof, lean_grind_mk_heq_proof,
    lean_grind_process_new_facts,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_13, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__0_value) as *mut LeanObject,7699194985028780469 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 98, 115, 116, 114, 97, 99, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__5_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__6_value) as *mut LeanObject,17040932255416921605 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 111, 118, 101, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__0_value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__1_value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__2_value) as *mut LeanObject,6936347780346814288 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__4_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 98, 115, 116, 114, 97, 99, 116, 58, 32, 40, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [41, 32, 61, 32, 40, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_proveEq_x3f___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_proveEq_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_proveEq_x3f___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_proveEq_x3f___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_proveEq_x3f___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(
    mut v_e_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_unused_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1911_ = l_Lean_Expr_hasMVar(v_e_1908_);
                if v___x_1911_ == 0 {
                    v___x_1912_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1912_, 0, v_e_1908_);
                    return v___x_1912_;
                } else {
                    v___x_1913_ = lean_st_ref_get(v___y_1909_);
                    v_mctx_1914_ = lean_ctor_get(v___x_1913_, 0);
                    lean_inc_ref(v_mctx_1914_);
                    lean_dec(v___x_1913_);
                    v___x_1915_ = l_Lean_instantiateMVarsCore(v_mctx_1914_, v_e_1908_);
                    v_fst_1916_ = lean_ctor_get(v___x_1915_, 0);
                    lean_inc(v_fst_1916_);
                    v_snd_1917_ = lean_ctor_get(v___x_1915_, 1);
                    lean_inc(v_snd_1917_);
                    lean_dec_ref(v___x_1915_);
                    v___x_1918_ = lean_st_ref_take(v___y_1909_);
                    v_cache_1919_ = lean_ctor_get(v___x_1918_, 1);
                    v_zetaDeltaFVarIds_1920_ = lean_ctor_get(v___x_1918_, 2);
                    v_postponed_1921_ = lean_ctor_get(v___x_1918_, 3);
                    v_diag_1922_ = lean_ctor_get(v___x_1918_, 4);
                    v_isSharedCheck_1931_ = (!lean_is_exclusive(v___x_1918_)) as u8;
                    if v_isSharedCheck_1931_ == 0 {
                        v_unused_1932_ = lean_ctor_get(v___x_1918_, 0);
                        lean_dec(v_unused_1932_);
                        v___x_1924_ = v___x_1918_;
                        v_isShared_1925_ = v_isSharedCheck_1931_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1922_);
                        lean_inc(v_postponed_1921_);
                        lean_inc(v_zetaDeltaFVarIds_1920_);
                        lean_inc(v_cache_1919_);
                        lean_dec(v___x_1918_);
                        v___x_1924_ = lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1925_ == 0 {
                    lean_ctor_set(v___x_1924_, 0, v_snd_1917_);
                    v___x_1927_ = v___x_1924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_snd_1917_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_cache_1919_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_zetaDeltaFVarIds_1920_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_postponed_1921_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_diag_1922_);
                    v___x_1927_ = v_reuseFailAlloc_1930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1928_ = lean_st_ref_set(v___y_1909_, v___x_1927_);
                v___x_1929_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1929_, 0, v_fst_1916_);
                return v___x_1929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg___boxed(
    mut v_e_1933_: *mut LeanObject,
    mut v___y_1934_: *mut LeanObject,
    mut v___y_1935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1936_: *mut LeanObject = core::ptr::null_mut();
    v_res_1936_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1933_, v___y_1934_);
    lean_dec(v___y_1934_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(
    mut v_e_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1937_, v___y_1945_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___boxed(
    mut v_e_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1962_: *mut LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0(v_e_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
    lean_dec(v___y_1960_);
    lean_dec_ref(v___y_1959_);
    lean_dec(v___y_1958_);
    lean_dec_ref(v___y_1957_);
    lean_dec(v___y_1956_);
    lean_dec_ref(v___y_1955_);
    lean_dec(v___y_1954_);
    lean_dec_ref(v___y_1953_);
    lean_dec(v___y_1952_);
    lean_dec(v___y_1951_);
    return v_res_1962_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(
    mut v_e_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
    mut v_a_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut v_unused_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1975_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1963_, v_a_1964_);
                if lean_obj_tag(v___x_1975_) == 0 {
                    v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2007_ = (!lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2007_ == 0 {
                        v___x_1978_ = v___x_1975_;
                        v_isShared_1979_ = v_isSharedCheck_2007_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1976_);
                        lean_dec(v___x_1975_);
                        v___x_1978_ = lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_2007_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1963_);
                    v_a_2008_ = lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2015_ = (!lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v___x_2010_ = v___x_1975_;
                        v_isShared_2011_ = v_isSharedCheck_2015_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2008_);
                        lean_dec(v___x_1975_);
                        v___x_2010_ = lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2015_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1980_ = (lean_unbox(v_a_1976_) as u8);
                lean_dec(v_a_1976_);
                if v___x_1980_ == 0 {
                    lean_del_object(v___x_1978_);
                    v___x_1981_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized_spec__0___redArg(v_e_1963_, v_a_1971_);
                    v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
                    lean_inc(v_a_1982_);
                    lean_dec_ref(v___x_1981_);
                    v___x_1983_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                        v_a_1982_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_,
                        v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_,
                    );
                    if lean_obj_tag(v___x_1983_) == 0 {
                        v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
                        lean_inc_n(v_a_1984_, 2);
                        lean_dec_ref_known(v___x_1983_, 1);
                        v___x_1985_ = lean_unsigned_to_nat(0);
                        v___x_1986_ = lean_box(0);
                        lean_inc(v_a_1973_);
                        lean_inc_ref(v_a_1972_);
                        lean_inc(v_a_1971_);
                        lean_inc_ref(v_a_1970_);
                        lean_inc(v_a_1969_);
                        lean_inc_ref(v_a_1968_);
                        lean_inc(v_a_1967_);
                        lean_inc_ref(v_a_1966_);
                        lean_inc(v_a_1965_);
                        lean_inc(v_a_1964_);
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
                        if lean_obj_tag(v___x_1987_) == 0 {
                            v_isSharedCheck_1994_ = (!lean_is_exclusive(v___x_1987_)) as u8;
                            if v_isSharedCheck_1994_ == 0 {
                                v_unused_1995_ = lean_ctor_get(v___x_1987_, 0);
                                lean_dec(v_unused_1995_);
                                v___x_1989_ = v___x_1987_;
                                v_isShared_1990_ = v_isSharedCheck_1994_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_1987_);
                                v___x_1989_ = lean_box(0);
                                v_isShared_1990_ = v_isSharedCheck_1994_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1984_);
                            v_a_1996_ = lean_ctor_get(v___x_1987_, 0);
                            v_isSharedCheck_2003_ = (!lean_is_exclusive(v___x_1987_)) as u8;
                            if v_isSharedCheck_2003_ == 0 {
                                v___x_1998_ = v___x_1987_;
                                v_isShared_1999_ = v_isSharedCheck_2003_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1996_);
                                lean_dec(v___x_1987_);
                                v___x_1998_ = lean_box(0);
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
                        lean_ctor_set(v___x_1978_, 0, v_e_1963_);
                        v___x_2005_ = v___x_1978_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_e_1963_);
                        v___x_2005_ = v_reuseFailAlloc_2006_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1990_ == 0 {
                    lean_ctor_set(v___x_1989_, 0, v_a_1984_);
                    v___x_1992_ = v___x_1989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1984_);
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
                    v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
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
                    v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
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
    mut v_e_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
    mut v_a_2020_: *mut LeanObject,
    mut v_a_2021_: *mut LeanObject,
    mut v_a_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
    mut v_a_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2028_: *mut LeanObject = core::ptr::null_mut();
    v_res_2028_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(
        v_e_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_,
        v_a_2024_, v_a_2025_, v_a_2026_,
    );
    lean_dec(v_a_2026_);
    lean_dec_ref(v_a_2025_);
    lean_dec(v_a_2024_);
    lean_dec_ref(v_a_2023_);
    lean_dec(v_a_2022_);
    lean_dec_ref(v_a_2021_);
    lean_dec(v_a_2020_);
    lean_dec_ref(v_a_2019_);
    lean_dec(v_a_2018_);
    lean_dec(v_a_2017_);
    return v_res_2028_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
    mut v_a_2029_: *mut LeanObject,
    mut v_a_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    v___x_2032_ = lean_unsigned_to_nat(0);
    v___x_2033_ = lean_nat_dec_lt(v___x_2032_, v_a_2029_);
    v___x_2034_ = lean_box((v___x_2033_) as usize);
    v___x_2035_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2035_, 0, v___x_2034_);
    lean_ctor_set(v___x_2035_, 1, v_a_2030_);
    v___x_2036_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2036_, 0, v___x_2035_);
    v___x_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2037_, 0, v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg___boxed(
    mut v_a_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
    mut v_a_2040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2041_: *mut LeanObject = core::ptr::null_mut();
    v_res_2041_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
        v_a_2038_, v_a_2039_,
    );
    lean_dec(v_a_2038_);
    return v_res_2041_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(
    mut v_a_2042_: *mut LeanObject,
    mut v_a_2043_: *mut LeanObject,
    mut v_a_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
    mut v_a_2046_: *mut LeanObject,
    mut v_a_2047_: *mut LeanObject,
    mut v_a_2048_: *mut LeanObject,
    mut v_a_2049_: *mut LeanObject,
    mut v_a_2050_: *mut LeanObject,
    mut v_a_2051_: *mut LeanObject,
    mut v_a_2052_: *mut LeanObject,
    mut v_a_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
        v_a_2042_, v_a_2043_,
    );
    return v___x_2055_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___boxed(
    mut v_a_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_res_2069_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder(
        v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_,
        v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_,
    );
    lean_dec(v_a_2067_);
    lean_dec_ref(v_a_2066_);
    lean_dec(v_a_2065_);
    lean_dec_ref(v_a_2064_);
    lean_dec(v_a_2063_);
    lean_dec_ref(v_a_2062_);
    lean_dec(v_a_2061_);
    lean_dec_ref(v_a_2060_);
    lean_dec(v_a_2059_);
    lean_dec(v_a_2058_);
    lean_dec(v_a_2056_);
    return v_res_2069_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(
    mut v_x_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
    mut v_a_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    v___x_2084_ = lean_unsigned_to_nat(1);
    v___x_2085_ = lean_nat_add(v_a_2071_, v___x_2084_);
    lean_inc(v_a_2082_);
    lean_inc_ref(v_a_2081_);
    lean_inc(v_a_2080_);
    lean_inc_ref(v_a_2079_);
    lean_inc(v_a_2078_);
    lean_inc_ref(v_a_2077_);
    lean_inc(v_a_2076_);
    lean_inc_ref(v_a_2075_);
    lean_inc(v_a_2074_);
    lean_inc(v_a_2073_);
    v___x_2086_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_2086_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg___boxed(
    mut v_x_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
    mut v_a_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
    mut v_a_2094_: *mut LeanObject,
    mut v_a_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2101_: *mut LeanObject = core::ptr::null_mut();
    v_res_2101_ =
        l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___redArg(
            v_x_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_,
            v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_,
        );
    lean_dec(v_a_2099_);
    lean_dec_ref(v_a_2098_);
    lean_dec(v_a_2097_);
    lean_dec_ref(v_a_2096_);
    lean_dec(v_a_2095_);
    lean_dec_ref(v_a_2094_);
    lean_dec(v_a_2093_);
    lean_dec_ref(v_a_2092_);
    lean_dec(v_a_2091_);
    lean_dec(v_a_2090_);
    lean_dec(v_a_2088_);
    return v_res_2101_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset(
    mut v_00_u03b1_2102_: *mut LeanObject,
    mut v_x_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
    mut v_a_2111_: *mut LeanObject,
    mut v_a_2112_: *mut LeanObject,
    mut v_a_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
    mut v_a_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_unsigned_to_nat(1);
    v___x_2118_ = lean_nat_add(v_a_2104_, v___x_2117_);
    lean_inc(v_a_2115_);
    lean_inc_ref(v_a_2114_);
    lean_inc(v_a_2113_);
    lean_inc_ref(v_a_2112_);
    lean_inc(v_a_2111_);
    lean_inc_ref(v_a_2110_);
    lean_inc(v_a_2109_);
    lean_inc_ref(v_a_2108_);
    lean_inc(v_a_2107_);
    lean_inc(v_a_2106_);
    v___x_2119_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_2119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_withIncOffset___boxed(
    mut v_00_u03b1_2120_: *mut LeanObject,
    mut v_x_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
    mut v_a_2124_: *mut LeanObject,
    mut v_a_2125_: *mut LeanObject,
    mut v_a_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
    mut v_a_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2135_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2133_);
    lean_dec_ref(v_a_2132_);
    lean_dec(v_a_2131_);
    lean_dec_ref(v_a_2130_);
    lean_dec(v_a_2129_);
    lean_dec_ref(v_a_2128_);
    lean_dec(v_a_2127_);
    lean_dec_ref(v_a_2126_);
    lean_dec(v_a_2125_);
    lean_dec(v_a_2124_);
    lean_dec(v_a_2122_);
    return v_res_2135_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2()
-> *mut LeanObject {
    let mut v_i_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v_i_2139_ = lean_unsigned_to_nat(0);
    v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__1;
    v___x_2141_ = lean_name_append_index_after(v___x_2140_, v_i_2139_);
    return v___x_2141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(
    mut v_as_2142_: *mut LeanObject,
    mut v_sz_2143_: usize,
    mut v_i_2144_: usize,
    mut v_b_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2146_: u8 = 0;
    let mut v_a_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_2148_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0___closed__2);
                    v___x_2149_ = 0;
                    lean_inc(v_a_2147_);
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
    mut v_as_2154_: *mut LeanObject,
    mut v_sz_2155_: *mut LeanObject,
    mut v_i_2156_: *mut LeanObject,
    mut v_b_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2158_: usize = 0;
    let mut v_i_boxed_2159_: usize = 0;
    let mut v_res_2160_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2158_ = lean_unbox_usize(v_sz_2155_);
    lean_dec(v_sz_2155_);
    v_i_boxed_2159_ = lean_unbox_usize(v_i_2156_);
    lean_dec(v_i_2156_);
    v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_as_2154_, v_sz_boxed_2158_, v_i_boxed_2159_, v_b_2157_);
    lean_dec_ref(v_as_2154_);
    return v_res_2160_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(
    mut v_varTypes_2161_: *mut LeanObject,
    mut v_b_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2163_: usize = 0;
    let mut v___x_2164_: usize = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v_sz_2163_ = lean_array_size(v_varTypes_2161_);
    v___x_2164_ = 0usize;
    v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType_spec__0(v_varTypes_2161_, v_sz_2163_, v___x_2164_, v_b_2162_);
    return v___x_2165_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType___boxed(
    mut v_varTypes_2166_: *mut LeanObject,
    mut v_b_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2168_: *mut LeanObject = core::ptr::null_mut();
    v_res_2168_ =
        l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(
            v_varTypes_2166_,
            v_b_2167_,
        );
    lean_dec_ref(v_varTypes_2166_);
    return v_res_2168_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(
    mut v_a_2169_: *mut LeanObject,
    mut v_x_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2170_) == 0 {
                    v___x_2171_ = lean_box(0);
                    return v___x_2171_;
                } else {
                    v_key_2172_ = lean_ctor_get(v_x_2170_, 0);
                    v_value_2173_ = lean_ctor_get(v_x_2170_, 1);
                    v_tail_2174_ = lean_ctor_get(v_x_2170_, 2);
                    v_fst_2179_ = lean_ctor_get(v_key_2172_, 0);
                    v_snd_2180_ = lean_ctor_get(v_key_2172_, 1);
                    v_fst_2181_ = lean_ctor_get(v_a_2169_, 0);
                    v_snd_2182_ = lean_ctor_get(v_a_2169_, 1);
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
                    lean_inc(v_value_2173_);
                    v___x_2178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2178_, 0, v_value_2173_);
                    return v___x_2178_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg___boxed(
    mut v_a_2185_: *mut LeanObject,
    mut v_x_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2187_: *mut LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_2185_, v_x_2186_);
    lean_dec(v_x_2186_);
    lean_dec_ref(v_a_2185_);
    return v_res_2187_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(
    mut v_m_2188_: *mut LeanObject,
    mut v_a_2189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2190_ = lean_ctor_get(v_m_2188_, 1);
    v_fst_2191_ = lean_ctor_get(v_a_2189_, 0);
    v_snd_2192_ = lean_ctor_get(v_a_2189_, 1);
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
    mut v_m_2210_: *mut LeanObject,
    mut v_a_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2212_: *mut LeanObject = core::ptr::null_mut();
    v_res_2212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_2210_, v_a_2211_);
    lean_dec_ref(v_a_2211_);
    lean_dec_ref(v_m_2210_);
    return v_res_2212_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(
    mut v_a_2213_: *mut LeanObject,
    mut v_x_2214_: *mut LeanObject,
) -> u8 {
    let mut v___x_2215_: u8 = 0;
    let mut v_key_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: u8 = 0;
    let mut v_fst_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2214_) == 0 {
                    v___x_2215_ = 0;
                    return v___x_2215_;
                } else {
                    v_key_2216_ = lean_ctor_get(v_x_2214_, 0);
                    v_tail_2217_ = lean_ctor_get(v_x_2214_, 2);
                    v_fst_2221_ = lean_ctor_get(v_key_2216_, 0);
                    v_snd_2222_ = lean_ctor_get(v_key_2216_, 1);
                    v_fst_2223_ = lean_ctor_get(v_a_2213_, 0);
                    v_snd_2224_ = lean_ctor_get(v_a_2213_, 1);
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
    mut v_a_2227_: *mut LeanObject,
    mut v_x_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2229_: u8 = 0;
    let mut v_r_2230_: *mut LeanObject = core::ptr::null_mut();
    v_res_2229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_2227_, v_x_2228_);
    lean_dec(v_x_2228_);
    lean_dec_ref(v_a_2227_);
    v_r_2230_ = lean_box((v_res_2229_) as usize);
    return v_r_2230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(
    mut v_a_2231_: *mut LeanObject,
    mut v_b_2232_: *mut LeanObject,
    mut v_x_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2239_: u8 = 0;
    let mut v___y_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: u8 = 0;
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2233_) == 0 {
                    lean_dec(v_b_2232_);
                    lean_dec_ref(v_a_2231_);
                    return v_x_2233_;
                } else {
                    v_key_2234_ = lean_ctor_get(v_x_2233_, 0);
                    v_value_2235_ = lean_ctor_get(v_x_2233_, 1);
                    v_tail_2236_ = lean_ctor_get(v_x_2233_, 2);
                    v_isSharedCheck_2255_ = (!lean_is_exclusive(v_x_2233_)) as u8;
                    if v_isSharedCheck_2255_ == 0 {
                        v___x_2238_ = v_x_2233_;
                        v_isShared_2239_ = v_isSharedCheck_2255_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2236_);
                        lean_inc(v_value_2235_);
                        lean_inc(v_key_2234_);
                        lean_dec(v_x_2233_);
                        v___x_2238_ = lean_box(0);
                        v_isShared_2239_ = v_isSharedCheck_2255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2249_ = lean_ctor_get(v_key_2234_, 0);
                v_snd_2250_ = lean_ctor_get(v_key_2234_, 1);
                v_fst_2251_ = lean_ctor_get(v_a_2231_, 0);
                v_snd_2252_ = lean_ctor_get(v_a_2231_, 1);
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
                        lean_ctor_set(v___x_2238_, 2, v___x_2242_);
                        v___x_2244_ = v___x_2238_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_key_2234_);
                        lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_value_2235_);
                        lean_ctor_set(v_reuseFailAlloc_2245_, 2, v___x_2242_);
                        v___x_2244_ = v_reuseFailAlloc_2245_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2235_);
                    lean_dec(v_key_2234_);
                    if v_isShared_2239_ == 0 {
                        lean_ctor_set(v___x_2238_, 1, v_b_2232_);
                        lean_ctor_set(v___x_2238_, 0, v_a_2231_);
                        v___x_2247_ = v___x_2238_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2231_);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_b_2232_);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_tail_2236_);
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
    mut v_x_2256_: *mut LeanObject,
    mut v_x_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2263_: u8 = 0;
    let mut v_fst_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2257_) == 0 {
                    return v_x_2256_;
                } else {
                    v_key_2258_ = lean_ctor_get(v_x_2257_, 0);
                    v_value_2259_ = lean_ctor_get(v_x_2257_, 1);
                    v_tail_2260_ = lean_ctor_get(v_x_2257_, 2);
                    v_isSharedCheck_2287_ = (!lean_is_exclusive(v_x_2257_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2262_ = v_x_2257_;
                        v_isShared_2263_ = v_isSharedCheck_2287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2260_);
                        lean_inc(v_value_2259_);
                        lean_inc(v_key_2258_);
                        lean_dec(v_x_2257_);
                        v___x_2262_ = lean_box(0);
                        v_isShared_2263_ = v_isSharedCheck_2287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2264_ = lean_ctor_get(v_key_2258_, 0);
                v_snd_2265_ = lean_ctor_get(v_key_2258_, 1);
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
                lean_inc(v___x_2281_);
                if v_isShared_2263_ == 0 {
                    lean_ctor_set(v___x_2262_, 2, v___x_2281_);
                    v___x_2283_ = v___x_2262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_key_2258_);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_value_2259_);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 2, v___x_2281_);
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
    mut v_i_2288_: *mut LeanObject,
    mut v_source_2289_: *mut LeanObject,
    mut v_target_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v_es_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2291_ = lean_array_get_size(v_source_2289_);
                v___x_2292_ = lean_nat_dec_lt(v_i_2288_, v___x_2291_);
                if v___x_2292_ == 0 {
                    lean_dec_ref(v_source_2289_);
                    lean_dec(v_i_2288_);
                    return v_target_2290_;
                } else {
                    v_es_2293_ = lean_array_fget(v_source_2289_, v_i_2288_);
                    v___x_2294_ = lean_box(0);
                    v_source_2295_ = lean_array_fset(v_source_2289_, v_i_2288_, v___x_2294_);
                    v_target_2296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_target_2290_, v_es_2293_);
                    v___x_2297_ = lean_unsigned_to_nat(1);
                    v___x_2298_ = lean_nat_add(v_i_2288_, v___x_2297_);
                    lean_dec(v_i_2288_);
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
    mut v_data_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    v___x_2301_ = lean_array_get_size(v_data_2300_);
    v___x_2302_ = lean_unsigned_to_nat(2);
    v_nbuckets_2303_ = lean_nat_mul(v___x_2301_, v___x_2302_);
    v___x_2304_ = lean_unsigned_to_nat(0);
    v___x_2305_ = lean_box(0);
    v___x_2306_ = lean_mk_array(v_nbuckets_2303_, v___x_2305_);
    v___x_2307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v___x_2304_, v_data_2300_, v___x_2306_);
    return v___x_2307_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(
    mut v_m_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
    mut v_b_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v_fst_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: u8 = 0;
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v_val_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2311_ = lean_ctor_get(v_m_2308_, 0);
                v_buckets_2312_ = lean_ctor_get(v_m_2308_, 1);
                v_isSharedCheck_2359_ = (!lean_is_exclusive(v_m_2308_)) as u8;
                if v_isSharedCheck_2359_ == 0 {
                    v___x_2314_ = v_m_2308_;
                    v_isShared_2315_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2312_);
                    lean_inc(v_size_2311_);
                    lean_dec(v_m_2308_);
                    v___x_2314_ = lean_box(0);
                    v_isShared_2315_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2316_ = lean_ctor_get(v_a_2309_, 0);
                v_snd_2317_ = lean_ctor_get(v_a_2309_, 1);
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
                    v___x_2335_ = lean_unsigned_to_nat(1);
                    v_size_x27_2336_ = lean_nat_add(v_size_2311_, v___x_2335_);
                    lean_dec(v_size_2311_);
                    lean_inc(v_bkt_2333_);
                    v___x_2337_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2337_, 0, v_a_2309_);
                    lean_ctor_set(v___x_2337_, 1, v_b_2310_);
                    lean_ctor_set(v___x_2337_, 2, v_bkt_2333_);
                    v_buckets_x27_2338_ =
                        lean_array_uset(v_buckets_2312_, v___x_2332_, v___x_2337_);
                    v___x_2339_ = lean_unsigned_to_nat(4);
                    v___x_2340_ = lean_nat_mul(v_size_x27_2336_, v___x_2339_);
                    v___x_2341_ = lean_unsigned_to_nat(3);
                    v___x_2342_ = lean_nat_div(v___x_2340_, v___x_2341_);
                    lean_dec(v___x_2340_);
                    v___x_2343_ = lean_array_get_size(v_buckets_x27_2338_);
                    v___x_2344_ = lean_nat_dec_le(v___x_2342_, v___x_2343_);
                    lean_dec(v___x_2342_);
                    if v___x_2344_ == 0 {
                        v_val_2345_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_buckets_x27_2338_);
                        if v_isShared_2315_ == 0 {
                            lean_ctor_set(v___x_2314_, 1, v_val_2345_);
                            lean_ctor_set(v___x_2314_, 0, v_size_x27_2336_);
                            v___x_2347_ = v___x_2314_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_size_x27_2336_);
                            lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_val_2345_);
                            v___x_2347_ = v_reuseFailAlloc_2348_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2315_ == 0 {
                            lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2338_);
                            lean_ctor_set(v___x_2314_, 0, v_size_x27_2336_);
                            v___x_2350_ = v___x_2314_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_size_x27_2336_);
                            lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_buckets_x27_2338_);
                            v___x_2350_ = v_reuseFailAlloc_2351_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2333_);
                    v___x_2352_ = lean_box(0);
                    v_buckets_x27_2353_ =
                        lean_array_uset(v_buckets_2312_, v___x_2332_, v___x_2352_);
                    v___x_2354_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_2309_, v_b_2310_, v_bkt_2333_);
                    v___x_2355_ = lean_array_uset(v_buckets_x27_2353_, v___x_2332_, v___x_2354_);
                    if v_isShared_2315_ == 0 {
                        lean_ctor_set(v___x_2314_, 1, v___x_2355_);
                        v___x_2357_ = v___x_2314_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_size_2311_);
                        lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2355_);
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
    mut v_lhs_2360_: *mut LeanObject,
    mut v_rhs_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
    mut v_a_2363_: *mut LeanObject,
    mut v_a_2364_: *mut LeanObject,
    mut v_a_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
    mut v_a_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v_val_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v_fst_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut v_unused_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v_fst_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v_val_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2470_: u8 = 0;
    let mut v_fst_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2486_: u8 = 0;
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_unused_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2497_: u8 = 0;
    let mut v_binderType_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v_val_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v_fst_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_unused_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2542_: u8 = 0;
    let mut v_binderType_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v_val_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v_fst_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_unused_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_2588_: u8 = 0;
    let mut v_type_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2608_: u8 = 0;
    let mut v_val_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v_fst_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2628_: u8 = 0;
    let mut v_isSharedCheck_2629_: u8 = 0;
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_unused_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v_val_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v_fst_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_unused_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: u8 = 0;
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v_cache_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varTypes_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhss_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhss_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2712_: u8 = 0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_isSharedCheck_2732_: u8 = 0;
    let mut v_a_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_a_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_a_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut v_a_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2760_: u8 = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2764_: u8 = 0;
    let mut v_a_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut v_a_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2423_ =
                    l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_inBinder___redArg(
                        v_a_2362_, v_a_2363_,
                    );
                if lean_obj_tag(v___x_2423_) == 0 {
                    v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2783_ = (!lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v___x_2426_ = v___x_2423_;
                        v_isShared_2427_ = v_isSharedCheck_2783_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2424_);
                        lean_dec(v___x_2423_);
                        v___x_2426_ = lean_box(0);
                        v_isShared_2427_ = v_isSharedCheck_2783_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_rhs_2361_);
                    lean_dec_ref(v_lhs_2360_);
                    v_a_2784_ = lean_ctor_get(v___x_2423_, 0);
                    v_isSharedCheck_2791_ = (!lean_is_exclusive(v___x_2423_)) as u8;
                    if v_isSharedCheck_2791_ == 0 {
                        v___x_2786_ = v___x_2423_;
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 68;
                        continue;
                    } else {
                        lean_inc(v_a_2784_);
                        lean_dec(v___x_2423_);
                        v___x_2786_ = lean_box(0);
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 68;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2392_ == 0 {
                    lean_dec(v___y_2389_);
                    lean_dec_ref(v___y_2388_);
                    lean_dec_ref(v___y_2386_);
                    lean_dec_ref(v___y_2382_);
                    lean_dec(v___y_2376_);
                    v___x_2393_ = lean_box(0);
                    v___x_2394_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2394_, 0, v___x_2393_);
                    return v___x_2394_;
                } else {
                    v___x_2395_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v___y_2382_, v___y_2388_, v___y_2379_, v___y_2386_, v___y_2390_, v___y_2387_, v___y_2383_, v___y_2391_, v___y_2381_, v___y_2377_, v___y_2384_, v___y_2385_, v___y_2378_, v___y_2380_);
                    if lean_obj_tag(v___x_2395_) == 0 {
                        v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
                        lean_inc(v_a_2396_);
                        if lean_obj_tag(v_a_2396_) == 0 {
                            lean_dec(v___y_2389_);
                            lean_dec(v___y_2376_);
                            return v___x_2395_;
                        } else {
                            v_isSharedCheck_2421_ = (!lean_is_exclusive(v___x_2395_)) as u8;
                            if v_isSharedCheck_2421_ == 0 {
                                v_unused_2422_ = lean_ctor_get(v___x_2395_, 0);
                                lean_dec(v_unused_2422_);
                                v___x_2398_ = v___x_2395_;
                                v_isShared_2399_ = v_isSharedCheck_2421_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_2395_);
                                v___x_2398_ = lean_box(0);
                                v_isShared_2399_ = v_isSharedCheck_2421_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_2389_);
                        lean_dec(v___y_2376_);
                        return v___x_2395_;
                    }
                }
            }
            2 => {
                v_val_2400_ = lean_ctor_get(v_a_2396_, 0);
                v_isSharedCheck_2420_ = (!lean_is_exclusive(v_a_2396_)) as u8;
                if v_isSharedCheck_2420_ == 0 {
                    v___x_2402_ = v_a_2396_;
                    v_isShared_2403_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_val_2400_);
                    lean_dec(v_a_2396_);
                    v___x_2402_ = lean_box(0);
                    v_isShared_2403_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_2404_ = lean_ctor_get(v_val_2400_, 0);
                v_snd_2405_ = lean_ctor_get(v_val_2400_, 1);
                v_isSharedCheck_2419_ = (!lean_is_exclusive(v_val_2400_)) as u8;
                if v_isSharedCheck_2419_ == 0 {
                    v___x_2407_ = v_val_2400_;
                    v_isShared_2408_ = v_isSharedCheck_2419_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2405_);
                    lean_inc(v_fst_2404_);
                    lean_dec(v_val_2400_);
                    v___x_2407_ = lean_box(0);
                    v_isShared_2408_ = v_isSharedCheck_2419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2409_ = l_Lean_Expr_proj___override(v___y_2389_, v___y_2376_, v_fst_2404_);
                if v_isShared_2408_ == 0 {
                    lean_ctor_set(v___x_2407_, 0, v___x_2409_);
                    v___x_2411_ = v___x_2407_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2409_);
                    lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_snd_2405_);
                    v___x_2411_ = v_reuseFailAlloc_2418_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2403_ == 0 {
                    lean_ctor_set(v___x_2402_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2402_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2411_);
                    v___x_2413_ = v_reuseFailAlloc_2417_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2399_ == 0 {
                    lean_ctor_set(v___x_2398_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2398_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
                    v___x_2415_ = v_reuseFailAlloc_2416_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2415_;
            }
            8 => {
                if lean_obj_tag(v_a_2424_) == 0 {
                    lean_dec_ref(v_rhs_2361_);
                    lean_dec_ref(v_lhs_2360_);
                    v___x_2428_ = lean_box(0);
                    if v_isShared_2427_ == 0 {
                        lean_ctor_set(v___x_2426_, 0, v___x_2428_);
                        v___x_2430_ = v___x_2426_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
                        v___x_2430_ = v_reuseFailAlloc_2431_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_val_2432_ = lean_ctor_get(v_a_2424_, 0);
                    v_isSharedCheck_2782_ = (!lean_is_exclusive(v_a_2424_)) as u8;
                    if v_isSharedCheck_2782_ == 0 {
                        v___x_2434_ = v_a_2424_;
                        v_isShared_2435_ = v_isSharedCheck_2782_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_val_2432_);
                        lean_dec(v_a_2424_);
                        v___x_2434_ = lean_box(0);
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
                v_fst_2436_ = lean_ctor_get(v_val_2432_, 0);
                v_snd_2437_ = lean_ctor_get(v_val_2432_, 1);
                v_isSharedCheck_2781_ = (!lean_is_exclusive(v_val_2432_)) as u8;
                if v_isSharedCheck_2781_ == 0 {
                    v___x_2439_ = v_val_2432_;
                    v_isShared_2440_ = v_isSharedCheck_2781_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_snd_2437_);
                    lean_inc(v_fst_2436_);
                    lean_dec(v_val_2432_);
                    v___x_2439_ = lean_box(0);
                    v_isShared_2440_ = v_isSharedCheck_2781_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2687_ = (lean_unbox(v_fst_2436_) as u8);
                lean_dec(v_fst_2436_);
                if v___x_2687_ == 0 {
                    lean_del_object(v___x_2439_);
                    lean_del_object(v___x_2434_);
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
                            lean_inc_ref(v_lhs_2360_);
                            v___x_2690_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_2360_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
                            if lean_obj_tag(v___x_2690_) == 0 {
                                v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
                                lean_inc(v_a_2691_);
                                lean_dec_ref_known(v___x_2690_, 1);
                                lean_inc_ref(v_rhs_2361_);
                                v___x_2692_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_2361_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
                                if lean_obj_tag(v___x_2692_) == 0 {
                                    v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
                                    lean_inc(v_a_2693_);
                                    lean_dec_ref_known(v___x_2692_, 1);
                                    lean_inc(v_a_2373_);
                                    lean_inc_ref(v_a_2372_);
                                    lean_inc(v_a_2371_);
                                    lean_inc_ref(v_a_2370_);
                                    lean_inc(v_a_2369_);
                                    lean_inc_ref(v_a_2368_);
                                    lean_inc(v_a_2367_);
                                    lean_inc_ref(v_a_2366_);
                                    lean_inc(v_a_2365_);
                                    lean_inc(v_a_2364_);
                                    v___x_2694_ = lean_grind_process_new_facts(
                                        v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_,
                                        v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_,
                                    );
                                    if lean_obj_tag(v___x_2694_) == 0 {
                                        lean_dec_ref_known(v___x_2694_, 1);
                                        v___x_2695_ = l_Lean_Meta_Grind_isEqv___redArg(
                                            v_a_2691_, v_a_2693_, v_a_2364_,
                                        );
                                        if lean_obj_tag(v___x_2695_) == 0 {
                                            v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
                                            lean_inc(v_a_2696_);
                                            lean_dec_ref_known(v___x_2695_, 1);
                                            v___x_2697_ = (lean_unbox(v_a_2696_) as u8);
                                            lean_dec(v_a_2696_);
                                            if v___x_2697_ == 0 {
                                                lean_dec(v_a_2693_);
                                                lean_dec(v_a_2691_);
                                                lean_del_object(v___x_2439_);
                                                lean_del_object(v___x_2434_);
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
                                                lean_inc(v_a_2693_);
                                                lean_inc(v_a_2691_);
                                                v___x_2698_ = l_Lean_Meta_Grind_hasSameType(
                                                    v_a_2691_, v_a_2693_, v_a_2370_, v_a_2371_,
                                                    v_a_2372_, v_a_2373_,
                                                );
                                                if lean_obj_tag(v___x_2698_) == 0 {
                                                    v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
                                                    lean_inc(v_a_2699_);
                                                    lean_dec_ref_known(v___x_2698_, 1);
                                                    v___x_2700_ = (lean_unbox(v_a_2699_) as u8);
                                                    lean_dec(v_a_2699_);
                                                    if v___x_2700_ == 0 {
                                                        lean_dec(v_a_2693_);
                                                        lean_dec(v_a_2691_);
                                                        lean_del_object(v___x_2439_);
                                                        lean_del_object(v___x_2434_);
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
                                                        lean_del_object(v___x_2426_);
                                                        lean_dec_ref(v_rhs_2361_);
                                                        lean_dec_ref(v_lhs_2360_);
                                                        lean_inc(v_a_2373_);
                                                        lean_inc_ref(v_a_2372_);
                                                        lean_inc(v_a_2371_);
                                                        lean_inc_ref(v_a_2370_);
                                                        lean_inc(v_a_2691_);
                                                        v___x_2701_ = lean_infer_type(
                                                            v_a_2691_, v_a_2370_, v_a_2371_,
                                                            v_a_2372_, v_a_2373_,
                                                        );
                                                        if lean_obj_tag(v___x_2701_) == 0 {
                                                            v_a_2702_ =
                                                                lean_ctor_get(v___x_2701_, 0);
                                                            v_isSharedCheck_2732_ =
                                                                (!lean_is_exclusive(v___x_2701_))
                                                                    as u8;
                                                            if v_isSharedCheck_2732_ == 0 {
                                                                v___x_2704_ = v___x_2701_;
                                                                v_isShared_2705_ =
                                                                    v_isSharedCheck_2732_;
                                                                state = 50;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2702_);
                                                                lean_dec(v___x_2701_);
                                                                v___x_2704_ = lean_box(0);
                                                                v_isShared_2705_ =
                                                                    v_isSharedCheck_2732_;
                                                                state = 50;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v_a_2693_);
                                                            lean_dec(v_a_2691_);
                                                            lean_del_object(v___x_2439_);
                                                            lean_dec(v_snd_2437_);
                                                            lean_del_object(v___x_2434_);
                                                            v_a_2733_ =
                                                                lean_ctor_get(v___x_2701_, 0);
                                                            v_isSharedCheck_2740_ =
                                                                (!lean_is_exclusive(v___x_2701_))
                                                                    as u8;
                                                            if v_isSharedCheck_2740_ == 0 {
                                                                v___x_2735_ = v___x_2701_;
                                                                v_isShared_2736_ =
                                                                    v_isSharedCheck_2740_;
                                                                state = 56;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2733_);
                                                                lean_dec(v___x_2701_);
                                                                v___x_2735_ = lean_box(0);
                                                                v_isShared_2736_ =
                                                                    v_isSharedCheck_2740_;
                                                                state = 56;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_a_2693_);
                                                    lean_dec(v_a_2691_);
                                                    lean_del_object(v___x_2439_);
                                                    lean_dec(v_snd_2437_);
                                                    lean_del_object(v___x_2434_);
                                                    lean_del_object(v___x_2426_);
                                                    lean_dec_ref(v_rhs_2361_);
                                                    lean_dec_ref(v_lhs_2360_);
                                                    v_a_2741_ = lean_ctor_get(v___x_2698_, 0);
                                                    v_isSharedCheck_2748_ =
                                                        (!lean_is_exclusive(v___x_2698_)) as u8;
                                                    if v_isSharedCheck_2748_ == 0 {
                                                        v___x_2743_ = v___x_2698_;
                                                        v_isShared_2744_ = v_isSharedCheck_2748_;
                                                        state = 58;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2741_);
                                                        lean_dec(v___x_2698_);
                                                        v___x_2743_ = lean_box(0);
                                                        v_isShared_2744_ = v_isSharedCheck_2748_;
                                                        state = 58;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_2693_);
                                            lean_dec(v_a_2691_);
                                            lean_del_object(v___x_2439_);
                                            lean_dec(v_snd_2437_);
                                            lean_del_object(v___x_2434_);
                                            lean_del_object(v___x_2426_);
                                            lean_dec_ref(v_rhs_2361_);
                                            lean_dec_ref(v_lhs_2360_);
                                            v_a_2749_ = lean_ctor_get(v___x_2695_, 0);
                                            v_isSharedCheck_2756_ =
                                                (!lean_is_exclusive(v___x_2695_)) as u8;
                                            if v_isSharedCheck_2756_ == 0 {
                                                v___x_2751_ = v___x_2695_;
                                                v_isShared_2752_ = v_isSharedCheck_2756_;
                                                state = 60;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2749_);
                                                lean_dec(v___x_2695_);
                                                v___x_2751_ = lean_box(0);
                                                v_isShared_2752_ = v_isSharedCheck_2756_;
                                                state = 60;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_2693_);
                                        lean_dec(v_a_2691_);
                                        lean_del_object(v___x_2439_);
                                        lean_dec(v_snd_2437_);
                                        lean_del_object(v___x_2434_);
                                        lean_del_object(v___x_2426_);
                                        lean_dec_ref(v_rhs_2361_);
                                        lean_dec_ref(v_lhs_2360_);
                                        v_a_2757_ = lean_ctor_get(v___x_2694_, 0);
                                        v_isSharedCheck_2764_ =
                                            (!lean_is_exclusive(v___x_2694_)) as u8;
                                        if v_isSharedCheck_2764_ == 0 {
                                            v___x_2759_ = v___x_2694_;
                                            v_isShared_2760_ = v_isSharedCheck_2764_;
                                            state = 62;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2757_);
                                            lean_dec(v___x_2694_);
                                            v___x_2759_ = lean_box(0);
                                            v_isShared_2760_ = v_isSharedCheck_2764_;
                                            state = 62;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2691_);
                                    lean_del_object(v___x_2439_);
                                    lean_dec(v_snd_2437_);
                                    lean_del_object(v___x_2434_);
                                    lean_del_object(v___x_2426_);
                                    lean_dec_ref(v_rhs_2361_);
                                    lean_dec_ref(v_lhs_2360_);
                                    v_a_2765_ = lean_ctor_get(v___x_2692_, 0);
                                    v_isSharedCheck_2772_ = (!lean_is_exclusive(v___x_2692_)) as u8;
                                    if v_isSharedCheck_2772_ == 0 {
                                        v___x_2767_ = v___x_2692_;
                                        v_isShared_2768_ = v_isSharedCheck_2772_;
                                        state = 64;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2765_);
                                        lean_dec(v___x_2692_);
                                        v___x_2767_ = lean_box(0);
                                        v_isShared_2768_ = v_isSharedCheck_2772_;
                                        state = 64;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_2439_);
                                lean_dec(v_snd_2437_);
                                lean_del_object(v___x_2434_);
                                lean_del_object(v___x_2426_);
                                lean_dec_ref(v_rhs_2361_);
                                lean_dec_ref(v_lhs_2360_);
                                v_a_2773_ = lean_ctor_get(v___x_2690_, 0);
                                v_isSharedCheck_2780_ = (!lean_is_exclusive(v___x_2690_)) as u8;
                                if v_isSharedCheck_2780_ == 0 {
                                    v___x_2775_ = v___x_2690_;
                                    v_isShared_2776_ = v_isSharedCheck_2780_;
                                    state = 66;
                                    continue;
                                } else {
                                    lean_inc(v_a_2773_);
                                    lean_dec(v___x_2690_);
                                    v___x_2775_ = lean_box(0);
                                    v_isShared_2776_ = v_isSharedCheck_2780_;
                                    state = 66;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_2439_);
                            lean_del_object(v___x_2434_);
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
                        lean_del_object(v___x_2439_);
                        lean_del_object(v___x_2434_);
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
            12 => match lean_obj_tag(v_lhs_2360_) {
                5 => {
                    if lean_obj_tag(v_rhs_2361_) == 5 {
                        lean_del_object(v___x_2426_);
                        v_fn_2453_ = lean_ctor_get(v_lhs_2360_, 0);
                        lean_inc_ref(v_fn_2453_);
                        v_arg_2454_ = lean_ctor_get(v_lhs_2360_, 1);
                        lean_inc_ref(v_arg_2454_);
                        lean_dec_ref_known(v_lhs_2360_, 2);
                        v_fn_2455_ = lean_ctor_get(v_rhs_2361_, 0);
                        lean_inc_ref(v_fn_2455_);
                        v_arg_2456_ = lean_ctor_get(v_rhs_2361_, 1);
                        lean_inc_ref(v_arg_2456_);
                        lean_dec_ref_known(v_rhs_2361_, 2);
                        v___x_2457_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_fn_2453_, v_fn_2455_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if lean_obj_tag(v___x_2457_) == 0 {
                            v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
                            lean_inc(v_a_2458_);
                            if lean_obj_tag(v_a_2458_) == 0 {
                                lean_dec_ref(v_arg_2456_);
                                lean_dec_ref(v_arg_2454_);
                                return v___x_2457_;
                            } else {
                                lean_dec_ref_known(v___x_2457_, 1);
                                v_val_2459_ = lean_ctor_get(v_a_2458_, 0);
                                lean_inc(v_val_2459_);
                                lean_dec_ref_known(v_a_2458_, 1);
                                v_fst_2460_ = lean_ctor_get(v_val_2459_, 0);
                                lean_inc(v_fst_2460_);
                                v_snd_2461_ = lean_ctor_get(v_val_2459_, 1);
                                lean_inc(v_snd_2461_);
                                lean_dec(v_val_2459_);
                                v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_arg_2454_, v_arg_2456_, v___y_2442_, v_snd_2461_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                if lean_obj_tag(v___x_2462_) == 0 {
                                    v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
                                    lean_inc(v_a_2463_);
                                    if lean_obj_tag(v_a_2463_) == 0 {
                                        lean_dec(v_fst_2460_);
                                        return v___x_2462_;
                                    } else {
                                        v_isSharedCheck_2488_ =
                                            (!lean_is_exclusive(v___x_2462_)) as u8;
                                        if v_isSharedCheck_2488_ == 0 {
                                            v_unused_2489_ = lean_ctor_get(v___x_2462_, 0);
                                            lean_dec(v_unused_2489_);
                                            v___x_2465_ = v___x_2462_;
                                            v_isShared_2466_ = v_isSharedCheck_2488_;
                                            state = 13;
                                            continue;
                                        } else {
                                            lean_dec(v___x_2462_);
                                            v___x_2465_ = lean_box(0);
                                            v_isShared_2466_ = v_isSharedCheck_2488_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_2460_);
                                    return v___x_2462_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_arg_2456_);
                            lean_dec_ref(v_arg_2454_);
                            return v___x_2457_;
                        }
                    } else {
                        lean_dec_ref_known(v_lhs_2360_, 2);
                        lean_dec(v_snd_2437_);
                        lean_dec_ref(v_rhs_2361_);
                        v___x_2490_ = lean_box(0);
                        if v_isShared_2427_ == 0 {
                            lean_ctor_set(v___x_2426_, 0, v___x_2490_);
                            v___x_2492_ = v___x_2426_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
                            v___x_2492_ = v_reuseFailAlloc_2493_;
                            state = 19;
                            continue;
                        }
                    }
                }
                6 => {
                    if lean_obj_tag(v_rhs_2361_) == 6 {
                        lean_del_object(v___x_2426_);
                        v_binderName_2494_ = lean_ctor_get(v_lhs_2360_, 0);
                        lean_inc(v_binderName_2494_);
                        v_binderType_2495_ = lean_ctor_get(v_lhs_2360_, 1);
                        lean_inc_ref(v_binderType_2495_);
                        v_body_2496_ = lean_ctor_get(v_lhs_2360_, 2);
                        lean_inc_ref(v_body_2496_);
                        v_binderInfo_2497_ = lean_ctor_get_uint8(
                            v_lhs_2360_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_dec_ref_known(v_lhs_2360_, 3);
                        v_binderType_2498_ = lean_ctor_get(v_rhs_2361_, 1);
                        lean_inc_ref(v_binderType_2498_);
                        v_body_2499_ = lean_ctor_get(v_rhs_2361_, 2);
                        lean_inc_ref(v_body_2499_);
                        lean_dec_ref_known(v_rhs_2361_, 3);
                        v___x_2500_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_2495_, v_binderType_2498_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if lean_obj_tag(v___x_2500_) == 0 {
                            v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
                            lean_inc(v_a_2501_);
                            if lean_obj_tag(v_a_2501_) == 0 {
                                lean_dec_ref(v_body_2499_);
                                lean_dec_ref(v_body_2496_);
                                lean_dec(v_binderName_2494_);
                                return v___x_2500_;
                            } else {
                                lean_dec_ref_known(v___x_2500_, 1);
                                v_val_2502_ = lean_ctor_get(v_a_2501_, 0);
                                lean_inc(v_val_2502_);
                                lean_dec_ref_known(v_a_2501_, 1);
                                v_fst_2503_ = lean_ctor_get(v_val_2502_, 0);
                                lean_inc(v_fst_2503_);
                                v_snd_2504_ = lean_ctor_get(v_val_2502_, 1);
                                lean_inc(v_snd_2504_);
                                lean_dec(v_val_2502_);
                                v___x_2505_ = lean_unsigned_to_nat(1);
                                v___x_2506_ = lean_nat_add(v___y_2442_, v___x_2505_);
                                v___x_2507_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_2496_, v_body_2499_, v___x_2506_, v_snd_2504_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                lean_dec(v___x_2506_);
                                if lean_obj_tag(v___x_2507_) == 0 {
                                    v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
                                    lean_inc(v_a_2508_);
                                    if lean_obj_tag(v_a_2508_) == 0 {
                                        lean_dec(v_fst_2503_);
                                        lean_dec(v_binderName_2494_);
                                        return v___x_2507_;
                                    } else {
                                        v_isSharedCheck_2533_ =
                                            (!lean_is_exclusive(v___x_2507_)) as u8;
                                        if v_isSharedCheck_2533_ == 0 {
                                            v_unused_2534_ = lean_ctor_get(v___x_2507_, 0);
                                            lean_dec(v_unused_2534_);
                                            v___x_2510_ = v___x_2507_;
                                            v_isShared_2511_ = v_isSharedCheck_2533_;
                                            state = 20;
                                            continue;
                                        } else {
                                            lean_dec(v___x_2507_);
                                            v___x_2510_ = lean_box(0);
                                            v_isShared_2511_ = v_isSharedCheck_2533_;
                                            state = 20;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_2503_);
                                    lean_dec(v_binderName_2494_);
                                    return v___x_2507_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_2499_);
                            lean_dec_ref(v_body_2496_);
                            lean_dec(v_binderName_2494_);
                            return v___x_2500_;
                        }
                    } else {
                        lean_dec_ref_known(v_lhs_2360_, 3);
                        lean_dec(v_snd_2437_);
                        lean_dec_ref(v_rhs_2361_);
                        v___x_2535_ = lean_box(0);
                        if v_isShared_2427_ == 0 {
                            lean_ctor_set(v___x_2426_, 0, v___x_2535_);
                            v___x_2537_ = v___x_2426_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
                            v___x_2537_ = v_reuseFailAlloc_2538_;
                            state = 26;
                            continue;
                        }
                    }
                }
                7 => {
                    if lean_obj_tag(v_rhs_2361_) == 7 {
                        lean_del_object(v___x_2426_);
                        v_binderName_2539_ = lean_ctor_get(v_lhs_2360_, 0);
                        lean_inc(v_binderName_2539_);
                        v_binderType_2540_ = lean_ctor_get(v_lhs_2360_, 1);
                        lean_inc_ref(v_binderType_2540_);
                        v_body_2541_ = lean_ctor_get(v_lhs_2360_, 2);
                        lean_inc_ref(v_body_2541_);
                        v_binderInfo_2542_ = lean_ctor_get_uint8(
                            v_lhs_2360_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_dec_ref_known(v_lhs_2360_, 3);
                        v_binderType_2543_ = lean_ctor_get(v_rhs_2361_, 1);
                        lean_inc_ref(v_binderType_2543_);
                        v_body_2544_ = lean_ctor_get(v_rhs_2361_, 2);
                        lean_inc_ref(v_body_2544_);
                        lean_dec_ref_known(v_rhs_2361_, 3);
                        v___x_2545_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_binderType_2540_, v_binderType_2543_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if lean_obj_tag(v___x_2545_) == 0 {
                            v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
                            lean_inc(v_a_2546_);
                            if lean_obj_tag(v_a_2546_) == 0 {
                                lean_dec_ref(v_body_2544_);
                                lean_dec_ref(v_body_2541_);
                                lean_dec(v_binderName_2539_);
                                return v___x_2545_;
                            } else {
                                lean_dec_ref_known(v___x_2545_, 1);
                                v_val_2547_ = lean_ctor_get(v_a_2546_, 0);
                                lean_inc(v_val_2547_);
                                lean_dec_ref_known(v_a_2546_, 1);
                                v_fst_2548_ = lean_ctor_get(v_val_2547_, 0);
                                lean_inc(v_fst_2548_);
                                v_snd_2549_ = lean_ctor_get(v_val_2547_, 1);
                                lean_inc(v_snd_2549_);
                                lean_dec(v_val_2547_);
                                v___x_2550_ = lean_unsigned_to_nat(1);
                                v___x_2551_ = lean_nat_add(v___y_2442_, v___x_2550_);
                                v___x_2552_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_2541_, v_body_2544_, v___x_2551_, v_snd_2549_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                lean_dec(v___x_2551_);
                                if lean_obj_tag(v___x_2552_) == 0 {
                                    v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
                                    lean_inc(v_a_2553_);
                                    if lean_obj_tag(v_a_2553_) == 0 {
                                        lean_dec(v_fst_2548_);
                                        lean_dec(v_binderName_2539_);
                                        return v___x_2552_;
                                    } else {
                                        v_isSharedCheck_2578_ =
                                            (!lean_is_exclusive(v___x_2552_)) as u8;
                                        if v_isSharedCheck_2578_ == 0 {
                                            v_unused_2579_ = lean_ctor_get(v___x_2552_, 0);
                                            lean_dec(v_unused_2579_);
                                            v___x_2555_ = v___x_2552_;
                                            v_isShared_2556_ = v_isSharedCheck_2578_;
                                            state = 27;
                                            continue;
                                        } else {
                                            lean_dec(v___x_2552_);
                                            v___x_2555_ = lean_box(0);
                                            v_isShared_2556_ = v_isSharedCheck_2578_;
                                            state = 27;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_2548_);
                                    lean_dec(v_binderName_2539_);
                                    return v___x_2552_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_2544_);
                            lean_dec_ref(v_body_2541_);
                            lean_dec(v_binderName_2539_);
                            return v___x_2545_;
                        }
                    } else {
                        lean_dec_ref_known(v_lhs_2360_, 3);
                        lean_dec(v_snd_2437_);
                        lean_dec_ref(v_rhs_2361_);
                        v___x_2580_ = lean_box(0);
                        if v_isShared_2427_ == 0 {
                            lean_ctor_set(v___x_2426_, 0, v___x_2580_);
                            v___x_2582_ = v___x_2426_;
                            state = 33;
                            continue;
                        } else {
                            v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
                            v___x_2582_ = v_reuseFailAlloc_2583_;
                            state = 33;
                            continue;
                        }
                    }
                }
                8 => {
                    if lean_obj_tag(v_rhs_2361_) == 8 {
                        lean_del_object(v___x_2426_);
                        v_declName_2584_ = lean_ctor_get(v_lhs_2360_, 0);
                        lean_inc(v_declName_2584_);
                        v_type_2585_ = lean_ctor_get(v_lhs_2360_, 1);
                        lean_inc_ref(v_type_2585_);
                        v_value_2586_ = lean_ctor_get(v_lhs_2360_, 2);
                        lean_inc_ref(v_value_2586_);
                        v_body_2587_ = lean_ctor_get(v_lhs_2360_, 3);
                        lean_inc_ref(v_body_2587_);
                        v_nondep_2588_ = lean_ctor_get_uint8(
                            v_lhs_2360_,
                            (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                        );
                        lean_dec_ref_known(v_lhs_2360_, 4);
                        v_type_2589_ = lean_ctor_get(v_rhs_2361_, 1);
                        lean_inc_ref(v_type_2589_);
                        v_value_2590_ = lean_ctor_get(v_rhs_2361_, 2);
                        lean_inc_ref(v_value_2590_);
                        v_body_2591_ = lean_ctor_get(v_rhs_2361_, 3);
                        lean_inc_ref(v_body_2591_);
                        lean_dec_ref_known(v_rhs_2361_, 4);
                        v___x_2592_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_type_2585_, v_type_2589_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if lean_obj_tag(v___x_2592_) == 0 {
                            v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
                            lean_inc(v_a_2593_);
                            if lean_obj_tag(v_a_2593_) == 0 {
                                lean_dec_ref(v_body_2591_);
                                lean_dec_ref(v_value_2590_);
                                lean_dec_ref(v_body_2587_);
                                lean_dec_ref(v_value_2586_);
                                lean_dec(v_declName_2584_);
                                return v___x_2592_;
                            } else {
                                lean_dec_ref_known(v___x_2592_, 1);
                                v_val_2594_ = lean_ctor_get(v_a_2593_, 0);
                                lean_inc(v_val_2594_);
                                lean_dec_ref_known(v_a_2593_, 1);
                                v_fst_2595_ = lean_ctor_get(v_val_2594_, 0);
                                lean_inc(v_fst_2595_);
                                v_snd_2596_ = lean_ctor_get(v_val_2594_, 1);
                                lean_inc(v_snd_2596_);
                                lean_dec(v_val_2594_);
                                v___x_2597_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_value_2586_, v_value_2590_, v___y_2442_, v_snd_2596_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                if lean_obj_tag(v___x_2597_) == 0 {
                                    v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
                                    lean_inc(v_a_2598_);
                                    if lean_obj_tag(v_a_2598_) == 0 {
                                        lean_dec(v_fst_2595_);
                                        lean_dec_ref(v_body_2591_);
                                        lean_dec_ref(v_body_2587_);
                                        lean_dec(v_declName_2584_);
                                        return v___x_2597_;
                                    } else {
                                        lean_dec_ref_known(v___x_2597_, 1);
                                        v_val_2599_ = lean_ctor_get(v_a_2598_, 0);
                                        lean_inc(v_val_2599_);
                                        lean_dec_ref_known(v_a_2598_, 1);
                                        v_fst_2600_ = lean_ctor_get(v_val_2599_, 0);
                                        lean_inc(v_fst_2600_);
                                        v_snd_2601_ = lean_ctor_get(v_val_2599_, 1);
                                        lean_inc(v_snd_2601_);
                                        lean_dec(v_val_2599_);
                                        v___x_2602_ = lean_unsigned_to_nat(1);
                                        v___x_2603_ = lean_nat_add(v___y_2442_, v___x_2602_);
                                        v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_body_2587_, v_body_2591_, v___x_2603_, v_snd_2601_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                                        lean_dec(v___x_2603_);
                                        if lean_obj_tag(v___x_2604_) == 0 {
                                            v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
                                            lean_inc(v_a_2605_);
                                            if lean_obj_tag(v_a_2605_) == 0 {
                                                lean_dec(v_fst_2600_);
                                                lean_dec(v_fst_2595_);
                                                lean_dec(v_declName_2584_);
                                                return v___x_2604_;
                                            } else {
                                                v_isSharedCheck_2630_ =
                                                    (!lean_is_exclusive(v___x_2604_)) as u8;
                                                if v_isSharedCheck_2630_ == 0 {
                                                    v_unused_2631_ = lean_ctor_get(v___x_2604_, 0);
                                                    lean_dec(v_unused_2631_);
                                                    v___x_2607_ = v___x_2604_;
                                                    v_isShared_2608_ = v_isSharedCheck_2630_;
                                                    state = 34;
                                                    continue;
                                                } else {
                                                    lean_dec(v___x_2604_);
                                                    v___x_2607_ = lean_box(0);
                                                    v_isShared_2608_ = v_isSharedCheck_2630_;
                                                    state = 34;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_fst_2600_);
                                            lean_dec(v_fst_2595_);
                                            lean_dec(v_declName_2584_);
                                            return v___x_2604_;
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_2595_);
                                    lean_dec_ref(v_body_2591_);
                                    lean_dec_ref(v_body_2587_);
                                    lean_dec(v_declName_2584_);
                                    return v___x_2597_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_2591_);
                            lean_dec_ref(v_value_2590_);
                            lean_dec_ref(v_body_2587_);
                            lean_dec_ref(v_value_2586_);
                            lean_dec(v_declName_2584_);
                            return v___x_2592_;
                        }
                    } else {
                        lean_dec_ref_known(v_lhs_2360_, 4);
                        lean_dec(v_snd_2437_);
                        lean_dec_ref(v_rhs_2361_);
                        v___x_2632_ = lean_box(0);
                        if v_isShared_2427_ == 0 {
                            lean_ctor_set(v___x_2426_, 0, v___x_2632_);
                            v___x_2634_ = v___x_2426_;
                            state = 40;
                            continue;
                        } else {
                            v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
                            v___x_2634_ = v_reuseFailAlloc_2635_;
                            state = 40;
                            continue;
                        }
                    }
                }
                10 => {
                    if lean_obj_tag(v_rhs_2361_) == 10 {
                        lean_del_object(v___x_2426_);
                        v_data_2636_ = lean_ctor_get(v_lhs_2360_, 0);
                        lean_inc(v_data_2636_);
                        v_expr_2637_ = lean_ctor_get(v_lhs_2360_, 1);
                        lean_inc_ref(v_expr_2637_);
                        lean_dec_ref_known(v_lhs_2360_, 2);
                        v_expr_2638_ = lean_ctor_get(v_rhs_2361_, 1);
                        lean_inc_ref(v_expr_2638_);
                        lean_dec_ref_known(v_rhs_2361_, 2);
                        v___x_2639_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_expr_2637_, v_expr_2638_, v___y_2442_, v_snd_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
                        if lean_obj_tag(v___x_2639_) == 0 {
                            v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
                            lean_inc(v_a_2640_);
                            if lean_obj_tag(v_a_2640_) == 0 {
                                lean_dec(v_data_2636_);
                                return v___x_2639_;
                            } else {
                                v_isSharedCheck_2665_ = (!lean_is_exclusive(v___x_2639_)) as u8;
                                if v_isSharedCheck_2665_ == 0 {
                                    v_unused_2666_ = lean_ctor_get(v___x_2639_, 0);
                                    lean_dec(v_unused_2666_);
                                    v___x_2642_ = v___x_2639_;
                                    v_isShared_2643_ = v_isSharedCheck_2665_;
                                    state = 41;
                                    continue;
                                } else {
                                    lean_dec(v___x_2639_);
                                    v___x_2642_ = lean_box(0);
                                    v_isShared_2643_ = v_isSharedCheck_2665_;
                                    state = 41;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_data_2636_);
                            return v___x_2639_;
                        }
                    } else {
                        lean_dec_ref_known(v_lhs_2360_, 2);
                        lean_dec(v_snd_2437_);
                        lean_dec_ref(v_rhs_2361_);
                        v___x_2667_ = lean_box(0);
                        if v_isShared_2427_ == 0 {
                            lean_ctor_set(v___x_2426_, 0, v___x_2667_);
                            v___x_2669_ = v___x_2426_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
                            v___x_2669_ = v_reuseFailAlloc_2670_;
                            state = 47;
                            continue;
                        }
                    }
                }
                11 => {
                    if lean_obj_tag(v_rhs_2361_) == 11 {
                        lean_del_object(v___x_2426_);
                        v_typeName_2671_ = lean_ctor_get(v_lhs_2360_, 0);
                        lean_inc(v_typeName_2671_);
                        v_idx_2672_ = lean_ctor_get(v_lhs_2360_, 1);
                        lean_inc(v_idx_2672_);
                        v_struct_2673_ = lean_ctor_get(v_lhs_2360_, 2);
                        lean_inc_ref(v_struct_2673_);
                        lean_dec_ref_known(v_lhs_2360_, 3);
                        v_typeName_2674_ = lean_ctor_get(v_rhs_2361_, 0);
                        lean_inc(v_typeName_2674_);
                        v_idx_2675_ = lean_ctor_get(v_rhs_2361_, 1);
                        lean_inc(v_idx_2675_);
                        v_struct_2676_ = lean_ctor_get(v_rhs_2361_, 2);
                        lean_inc_ref(v_struct_2676_);
                        lean_dec_ref_known(v_rhs_2361_, 3);
                        v___x_2677_ = lean_name_eq(v_typeName_2671_, v_typeName_2674_);
                        lean_dec(v_typeName_2674_);
                        if v___x_2677_ == 0 {
                            lean_dec(v_idx_2675_);
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
                            lean_dec(v_idx_2675_);
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
                        lean_dec_ref_known(v_lhs_2360_, 3);
                        lean_dec(v_snd_2437_);
                        lean_dec_ref(v_rhs_2361_);
                        v___x_2679_ = lean_box(0);
                        if v_isShared_2427_ == 0 {
                            lean_ctor_set(v___x_2426_, 0, v___x_2679_);
                            v___x_2681_ = v___x_2426_;
                            state = 48;
                            continue;
                        } else {
                            v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
                            v___x_2681_ = v_reuseFailAlloc_2682_;
                            state = 48;
                            continue;
                        }
                    }
                }
                _ => {
                    lean_dec(v_snd_2437_);
                    lean_dec_ref(v_rhs_2361_);
                    lean_dec_ref(v_lhs_2360_);
                    v___x_2683_ = lean_box(0);
                    if v_isShared_2427_ == 0 {
                        lean_ctor_set(v___x_2426_, 0, v___x_2683_);
                        v___x_2685_ = v___x_2426_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
                        v___x_2685_ = v_reuseFailAlloc_2686_;
                        state = 49;
                        continue;
                    }
                }
            },
            13 => {
                v_val_2467_ = lean_ctor_get(v_a_2463_, 0);
                v_isSharedCheck_2487_ = (!lean_is_exclusive(v_a_2463_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v___x_2469_ = v_a_2463_;
                    v_isShared_2470_ = v_isSharedCheck_2487_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_val_2467_);
                    lean_dec(v_a_2463_);
                    v___x_2469_ = lean_box(0);
                    v_isShared_2470_ = v_isSharedCheck_2487_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_fst_2471_ = lean_ctor_get(v_val_2467_, 0);
                v_snd_2472_ = lean_ctor_get(v_val_2467_, 1);
                v_isSharedCheck_2486_ = (!lean_is_exclusive(v_val_2467_)) as u8;
                if v_isSharedCheck_2486_ == 0 {
                    v___x_2474_ = v_val_2467_;
                    v_isShared_2475_ = v_isSharedCheck_2486_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_snd_2472_);
                    lean_inc(v_fst_2471_);
                    lean_dec(v_val_2467_);
                    v___x_2474_ = lean_box(0);
                    v_isShared_2475_ = v_isSharedCheck_2486_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2476_ = l_Lean_Expr_app___override(v_fst_2460_, v_fst_2471_);
                if v_isShared_2475_ == 0 {
                    lean_ctor_set(v___x_2474_, 0, v___x_2476_);
                    v___x_2478_ = v___x_2474_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2476_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_snd_2472_);
                    v___x_2478_ = v_reuseFailAlloc_2485_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2470_ == 0 {
                    lean_ctor_set(v___x_2469_, 0, v___x_2478_);
                    v___x_2480_ = v___x_2469_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2478_);
                    v___x_2480_ = v_reuseFailAlloc_2484_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2466_ == 0 {
                    lean_ctor_set(v___x_2465_, 0, v___x_2480_);
                    v___x_2482_ = v___x_2465_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
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
                v_val_2512_ = lean_ctor_get(v_a_2508_, 0);
                v_isSharedCheck_2532_ = (!lean_is_exclusive(v_a_2508_)) as u8;
                if v_isSharedCheck_2532_ == 0 {
                    v___x_2514_ = v_a_2508_;
                    v_isShared_2515_ = v_isSharedCheck_2532_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_val_2512_);
                    lean_dec(v_a_2508_);
                    v___x_2514_ = lean_box(0);
                    v_isShared_2515_ = v_isSharedCheck_2532_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v_fst_2516_ = lean_ctor_get(v_val_2512_, 0);
                v_snd_2517_ = lean_ctor_get(v_val_2512_, 1);
                v_isSharedCheck_2531_ = (!lean_is_exclusive(v_val_2512_)) as u8;
                if v_isSharedCheck_2531_ == 0 {
                    v___x_2519_ = v_val_2512_;
                    v_isShared_2520_ = v_isSharedCheck_2531_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_2517_);
                    lean_inc(v_fst_2516_);
                    lean_dec(v_val_2512_);
                    v___x_2519_ = lean_box(0);
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
                    lean_ctor_set(v___x_2519_, 0, v___x_2521_);
                    v___x_2523_ = v___x_2519_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2521_);
                    lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_snd_2517_);
                    v___x_2523_ = v_reuseFailAlloc_2530_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2515_ == 0 {
                    lean_ctor_set(v___x_2514_, 0, v___x_2523_);
                    v___x_2525_ = v___x_2514_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2523_);
                    v___x_2525_ = v_reuseFailAlloc_2529_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_2511_ == 0 {
                    lean_ctor_set(v___x_2510_, 0, v___x_2525_);
                    v___x_2527_ = v___x_2510_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
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
                v_val_2557_ = lean_ctor_get(v_a_2553_, 0);
                v_isSharedCheck_2577_ = (!lean_is_exclusive(v_a_2553_)) as u8;
                if v_isSharedCheck_2577_ == 0 {
                    v___x_2559_ = v_a_2553_;
                    v_isShared_2560_ = v_isSharedCheck_2577_;
                    state = 28;
                    continue;
                } else {
                    lean_inc(v_val_2557_);
                    lean_dec(v_a_2553_);
                    v___x_2559_ = lean_box(0);
                    v_isShared_2560_ = v_isSharedCheck_2577_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v_fst_2561_ = lean_ctor_get(v_val_2557_, 0);
                v_snd_2562_ = lean_ctor_get(v_val_2557_, 1);
                v_isSharedCheck_2576_ = (!lean_is_exclusive(v_val_2557_)) as u8;
                if v_isSharedCheck_2576_ == 0 {
                    v___x_2564_ = v_val_2557_;
                    v_isShared_2565_ = v_isSharedCheck_2576_;
                    state = 29;
                    continue;
                } else {
                    lean_inc(v_snd_2562_);
                    lean_inc(v_fst_2561_);
                    lean_dec(v_val_2557_);
                    v___x_2564_ = lean_box(0);
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
                    lean_ctor_set(v___x_2564_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2564_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2566_);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_snd_2562_);
                    v___x_2568_ = v_reuseFailAlloc_2575_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_2560_ == 0 {
                    lean_ctor_set(v___x_2559_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2559_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2574_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 0, v___x_2570_);
                    v___x_2572_ = v___x_2555_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
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
                v_val_2609_ = lean_ctor_get(v_a_2605_, 0);
                v_isSharedCheck_2629_ = (!lean_is_exclusive(v_a_2605_)) as u8;
                if v_isSharedCheck_2629_ == 0 {
                    v___x_2611_ = v_a_2605_;
                    v_isShared_2612_ = v_isSharedCheck_2629_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_val_2609_);
                    lean_dec(v_a_2605_);
                    v___x_2611_ = lean_box(0);
                    v_isShared_2612_ = v_isSharedCheck_2629_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v_fst_2613_ = lean_ctor_get(v_val_2609_, 0);
                v_snd_2614_ = lean_ctor_get(v_val_2609_, 1);
                v_isSharedCheck_2628_ = (!lean_is_exclusive(v_val_2609_)) as u8;
                if v_isSharedCheck_2628_ == 0 {
                    v___x_2616_ = v_val_2609_;
                    v_isShared_2617_ = v_isSharedCheck_2628_;
                    state = 36;
                    continue;
                } else {
                    lean_inc(v_snd_2614_);
                    lean_inc(v_fst_2613_);
                    lean_dec(v_val_2609_);
                    v___x_2616_ = lean_box(0);
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
                    lean_ctor_set(v___x_2616_, 0, v___x_2618_);
                    v___x_2620_ = v___x_2616_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2618_);
                    lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_snd_2614_);
                    v___x_2620_ = v_reuseFailAlloc_2627_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2612_ == 0 {
                    lean_ctor_set(v___x_2611_, 0, v___x_2620_);
                    v___x_2622_ = v___x_2611_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2620_);
                    v___x_2622_ = v_reuseFailAlloc_2626_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_2608_ == 0 {
                    lean_ctor_set(v___x_2607_, 0, v___x_2622_);
                    v___x_2624_ = v___x_2607_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
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
                v_val_2644_ = lean_ctor_get(v_a_2640_, 0);
                v_isSharedCheck_2664_ = (!lean_is_exclusive(v_a_2640_)) as u8;
                if v_isSharedCheck_2664_ == 0 {
                    v___x_2646_ = v_a_2640_;
                    v_isShared_2647_ = v_isSharedCheck_2664_;
                    state = 42;
                    continue;
                } else {
                    lean_inc(v_val_2644_);
                    lean_dec(v_a_2640_);
                    v___x_2646_ = lean_box(0);
                    v_isShared_2647_ = v_isSharedCheck_2664_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v_fst_2648_ = lean_ctor_get(v_val_2644_, 0);
                v_snd_2649_ = lean_ctor_get(v_val_2644_, 1);
                v_isSharedCheck_2663_ = (!lean_is_exclusive(v_val_2644_)) as u8;
                if v_isSharedCheck_2663_ == 0 {
                    v___x_2651_ = v_val_2644_;
                    v_isShared_2652_ = v_isSharedCheck_2663_;
                    state = 43;
                    continue;
                } else {
                    lean_inc(v_snd_2649_);
                    lean_inc(v_fst_2648_);
                    lean_dec(v_val_2644_);
                    v___x_2651_ = lean_box(0);
                    v_isShared_2652_ = v_isSharedCheck_2663_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_2653_ = l_Lean_Expr_mdata___override(v_data_2636_, v_fst_2648_);
                if v_isShared_2652_ == 0 {
                    lean_ctor_set(v___x_2651_, 0, v___x_2653_);
                    v___x_2655_ = v___x_2651_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2653_);
                    lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_snd_2649_);
                    v___x_2655_ = v_reuseFailAlloc_2662_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2647_ == 0 {
                    lean_ctor_set(v___x_2646_, 0, v___x_2655_);
                    v___x_2657_ = v___x_2646_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2655_);
                    v___x_2657_ = v_reuseFailAlloc_2661_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_2643_ == 0 {
                    lean_ctor_set(v___x_2642_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2642_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
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
                v_cache_2706_ = lean_ctor_get(v_snd_2437_, 0);
                v_varTypes_2707_ = lean_ctor_get(v_snd_2437_, 1);
                v_lhss_2708_ = lean_ctor_get(v_snd_2437_, 2);
                v_rhss_2709_ = lean_ctor_get(v_snd_2437_, 3);
                v_isSharedCheck_2731_ = (!lean_is_exclusive(v_snd_2437_)) as u8;
                if v_isSharedCheck_2731_ == 0 {
                    v___x_2711_ = v_snd_2437_;
                    v_isShared_2712_ = v_isSharedCheck_2731_;
                    state = 51;
                    continue;
                } else {
                    lean_inc(v_rhss_2709_);
                    lean_inc(v_lhss_2708_);
                    lean_inc(v_varTypes_2707_);
                    lean_inc(v_cache_2706_);
                    lean_dec(v_snd_2437_);
                    v___x_2711_ = lean_box(0);
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
                    lean_ctor_set(v___x_2711_, 3, v___x_2717_);
                    lean_ctor_set(v___x_2711_, 2, v___x_2716_);
                    lean_ctor_set(v___x_2711_, 1, v___x_2715_);
                    v___x_2719_ = v___x_2711_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_cache_2706_);
                    lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2715_);
                    lean_ctor_set(v_reuseFailAlloc_2730_, 2, v___x_2716_);
                    lean_ctor_set(v_reuseFailAlloc_2730_, 3, v___x_2717_);
                    v___x_2719_ = v_reuseFailAlloc_2730_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_2720_ = l_Lean_mkBVar(v___x_2714_);
                if v_isShared_2440_ == 0 {
                    lean_ctor_set(v___x_2439_, 1, v___x_2719_);
                    lean_ctor_set(v___x_2439_, 0, v___x_2720_);
                    v___x_2722_ = v___x_2439_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2720_);
                    lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2719_);
                    v___x_2722_ = v_reuseFailAlloc_2729_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_2435_ == 0 {
                    lean_ctor_set(v___x_2434_, 0, v___x_2722_);
                    v___x_2724_ = v___x_2434_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2722_);
                    v___x_2724_ = v_reuseFailAlloc_2728_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                if v_isShared_2705_ == 0 {
                    lean_ctor_set(v___x_2704_, 0, v___x_2724_);
                    v___x_2726_ = v___x_2704_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
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
                    v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
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
                    v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
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
                    v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
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
                    v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
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
                    v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
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
                    v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
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
                    v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
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
    mut v_lhs_2792_: *mut LeanObject,
    mut v_rhs_2793_: *mut LeanObject,
    mut v_a_2794_: *mut LeanObject,
    mut v_a_2795_: *mut LeanObject,
    mut v_a_2796_: *mut LeanObject,
    mut v_a_2797_: *mut LeanObject,
    mut v_a_2798_: *mut LeanObject,
    mut v_a_2799_: *mut LeanObject,
    mut v_a_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
    mut v_a_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
    mut v_a_2804_: *mut LeanObject,
    mut v_a_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2807_: u8 = 0;
    let mut v_cache_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v_val_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v_snd_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v_cache_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varTypes_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhss_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhss_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2841_: u8 = 0;
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2855_: u8 = 0;
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_isSharedCheck_2858_: u8 = 0;
    let mut v_unused_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
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
                    v_cache_2808_ = lean_ctor_get(v_a_2795_, 0);
                    lean_inc_ref(v_rhs_2793_);
                    lean_inc_ref(v_lhs_2792_);
                    v___x_2809_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2809_, 0, v_lhs_2792_);
                    lean_ctor_set(v___x_2809_, 1, v_rhs_2793_);
                    v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_cache_2808_, v___x_2809_);
                    if lean_obj_tag(v___x_2810_) == 1 {
                        lean_dec_ref_known(v___x_2809_, 2);
                        lean_dec_ref(v_rhs_2793_);
                        lean_dec_ref(v_lhs_2792_);
                        v_val_2811_ = lean_ctor_get(v___x_2810_, 0);
                        v_isSharedCheck_2820_ = (!lean_is_exclusive(v___x_2810_)) as u8;
                        if v_isSharedCheck_2820_ == 0 {
                            v___x_2813_ = v___x_2810_;
                            v_isShared_2814_ = v_isSharedCheck_2820_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2811_);
                            lean_dec(v___x_2810_);
                            v___x_2813_ = lean_box(0);
                            v_isShared_2814_ = v_isSharedCheck_2820_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2810_);
                        v___x_2821_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_2792_, v_rhs_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
                        if lean_obj_tag(v___x_2821_) == 0 {
                            v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
                            lean_inc(v_a_2822_);
                            if lean_obj_tag(v_a_2822_) == 0 {
                                lean_dec_ref_known(v___x_2809_, 2);
                                return v___x_2821_;
                            } else {
                                v_isSharedCheck_2858_ = (!lean_is_exclusive(v___x_2821_)) as u8;
                                if v_isSharedCheck_2858_ == 0 {
                                    v_unused_2859_ = lean_ctor_get(v___x_2821_, 0);
                                    lean_dec(v_unused_2859_);
                                    v___x_2824_ = v___x_2821_;
                                    v_isShared_2825_ = v_isSharedCheck_2858_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v___x_2821_);
                                    v___x_2824_ = lean_box(0);
                                    v_isShared_2825_ = v_isSharedCheck_2858_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v___x_2809_, 2);
                            return v___x_2821_;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_2793_);
                    v___x_2860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2860_, 0, v_lhs_2792_);
                    lean_ctor_set(v___x_2860_, 1, v_a_2795_);
                    v___x_2861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2861_, 0, v___x_2860_);
                    v___x_2862_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2862_, 0, v___x_2861_);
                    return v___x_2862_;
                }
            }
            1 => {
                v___x_2815_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2815_, 0, v_val_2811_);
                lean_ctor_set(v___x_2815_, 1, v_a_2795_);
                if v_isShared_2814_ == 0 {
                    lean_ctor_set(v___x_2813_, 0, v___x_2815_);
                    v___x_2817_ = v___x_2813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2815_);
                    v___x_2817_ = v_reuseFailAlloc_2819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2818_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2818_, 0, v___x_2817_);
                return v___x_2818_;
            }
            3 => {
                v_val_2826_ = lean_ctor_get(v_a_2822_, 0);
                v_isSharedCheck_2857_ = (!lean_is_exclusive(v_a_2822_)) as u8;
                if v_isSharedCheck_2857_ == 0 {
                    v___x_2828_ = v_a_2822_;
                    v_isShared_2829_ = v_isSharedCheck_2857_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_2826_);
                    lean_dec(v_a_2822_);
                    v___x_2828_ = lean_box(0);
                    v_isShared_2829_ = v_isSharedCheck_2857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_2830_ = lean_ctor_get(v_val_2826_, 1);
                v_fst_2831_ = lean_ctor_get(v_val_2826_, 0);
                v_isSharedCheck_2856_ = (!lean_is_exclusive(v_val_2826_)) as u8;
                if v_isSharedCheck_2856_ == 0 {
                    v___x_2833_ = v_val_2826_;
                    v_isShared_2834_ = v_isSharedCheck_2856_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_2830_);
                    lean_inc(v_fst_2831_);
                    lean_dec(v_val_2826_);
                    v___x_2833_ = lean_box(0);
                    v_isShared_2834_ = v_isSharedCheck_2856_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_cache_2835_ = lean_ctor_get(v_snd_2830_, 0);
                v_varTypes_2836_ = lean_ctor_get(v_snd_2830_, 1);
                v_lhss_2837_ = lean_ctor_get(v_snd_2830_, 2);
                v_rhss_2838_ = lean_ctor_get(v_snd_2830_, 3);
                v_isSharedCheck_2855_ = (!lean_is_exclusive(v_snd_2830_)) as u8;
                if v_isSharedCheck_2855_ == 0 {
                    v___x_2840_ = v_snd_2830_;
                    v_isShared_2841_ = v_isSharedCheck_2855_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_rhss_2838_);
                    lean_inc(v_lhss_2837_);
                    lean_inc(v_varTypes_2836_);
                    lean_inc(v_cache_2835_);
                    lean_dec(v_snd_2830_);
                    v___x_2840_ = lean_box(0);
                    v_isShared_2841_ = v_isSharedCheck_2855_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc(v_fst_2831_);
                v___x_2842_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_cache_2835_, v___x_2809_, v_fst_2831_);
                if v_isShared_2841_ == 0 {
                    lean_ctor_set(v___x_2840_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2842_);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_varTypes_2836_);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_lhss_2837_);
                    lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_rhss_2838_);
                    v___x_2844_ = v_reuseFailAlloc_2854_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2834_ == 0 {
                    lean_ctor_set(v___x_2833_, 1, v___x_2844_);
                    v___x_2846_ = v___x_2833_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_fst_2831_);
                    lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2844_);
                    v___x_2846_ = v_reuseFailAlloc_2853_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2829_ == 0 {
                    lean_ctor_set(v___x_2828_, 0, v___x_2846_);
                    v___x_2848_ = v___x_2828_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2846_);
                    v___x_2848_ = v_reuseFailAlloc_2852_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2825_ == 0 {
                    lean_ctor_set(v___x_2824_, 0, v___x_2848_);
                    v___x_2850_ = v___x_2824_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
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
    mut v_lhs_2863_: *mut LeanObject,
    mut v_rhs_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
    mut v_a_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
    mut v_a_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2878_: *mut LeanObject = core::ptr::null_mut();
    v_res_2878_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_lhs_2863_, v_rhs_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
    lean_dec(v_a_2876_);
    lean_dec_ref(v_a_2875_);
    lean_dec(v_a_2874_);
    lean_dec_ref(v_a_2873_);
    lean_dec(v_a_2872_);
    lean_dec_ref(v_a_2871_);
    lean_dec(v_a_2870_);
    lean_dec_ref(v_a_2869_);
    lean_dec(v_a_2868_);
    lean_dec(v_a_2867_);
    lean_dec(v_a_2865_);
    return v_res_2878_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore___boxed(
    mut v_lhs_2879_: *mut LeanObject,
    mut v_rhs_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
    mut v_a_2884_: *mut LeanObject,
    mut v_a_2885_: *mut LeanObject,
    mut v_a_2886_: *mut LeanObject,
    mut v_a_2887_: *mut LeanObject,
    mut v_a_2888_: *mut LeanObject,
    mut v_a_2889_: *mut LeanObject,
    mut v_a_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
    mut v_a_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2894_: *mut LeanObject = core::ptr::null_mut();
    v_res_2894_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_goCore(v_lhs_2879_, v_rhs_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
    lean_dec(v_a_2892_);
    lean_dec_ref(v_a_2891_);
    lean_dec(v_a_2890_);
    lean_dec_ref(v_a_2889_);
    lean_dec(v_a_2888_);
    lean_dec_ref(v_a_2887_);
    lean_dec(v_a_2886_);
    lean_dec_ref(v_a_2885_);
    lean_dec(v_a_2884_);
    lean_dec(v_a_2883_);
    lean_dec(v_a_2881_);
    return v_res_2894_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(
    mut v_00_u03b2_2895_: *mut LeanObject,
    mut v_m_2896_: *mut LeanObject,
    mut v_a_2897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    v___x_2898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___redArg(v_m_2896_, v_a_2897_);
    return v___x_2898_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1___boxed(
    mut v_00_u03b2_2899_: *mut LeanObject,
    mut v_m_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2902_: *mut LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1(v_00_u03b2_2899_, v_m_2900_, v_a_2901_);
    lean_dec_ref(v_a_2901_);
    lean_dec_ref(v_m_2900_);
    return v_res_2902_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2(
    mut v_00_u03b2_2903_: *mut LeanObject,
    mut v_m_2904_: *mut LeanObject,
    mut v_a_2905_: *mut LeanObject,
    mut v_b_2906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    v___x_2907_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2___redArg(v_m_2904_, v_a_2905_, v_b_2906_);
    return v___x_2907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(
    mut v_00_u03b2_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
    mut v_x_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    v___x_2911_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___redArg(v_a_2909_, v_x_2910_);
    return v___x_2911_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1___boxed(
    mut v_00_u03b2_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
    mut v_x_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2915_: *mut LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__1_spec__1(v_00_u03b2_2912_, v_a_2913_, v_x_2914_);
    lean_dec(v_x_2914_);
    lean_dec_ref(v_a_2913_);
    return v_res_2915_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(
    mut v_00_u03b2_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_x_2918_: *mut LeanObject,
) -> u8 {
    let mut v___x_2919_: u8 = 0;
    v___x_2919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___redArg(v_a_2917_, v_x_2918_);
    return v___x_2919_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3___boxed(
    mut v_00_u03b2_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_x_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2923_: u8 = 0;
    let mut v_r_2924_: *mut LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__3(v_00_u03b2_2920_, v_a_2921_, v_x_2922_);
    lean_dec(v_x_2922_);
    lean_dec_ref(v_a_2921_);
    v_r_2924_ = lean_box((v_res_2923_) as usize);
    return v_r_2924_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4(
    mut v_00_u03b2_2925_: *mut LeanObject,
    mut v_data_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    v___x_2927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4___redArg(v_data_2926_);
    return v___x_2927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5(
    mut v_00_u03b2_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_b_2930_: *mut LeanObject,
    mut v_x_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    v___x_2932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__5___redArg(v_a_2929_, v_b_2930_, v_x_2931_);
    return v___x_2932_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2933_: *mut LeanObject,
    mut v_i_2934_: *mut LeanObject,
    mut v_source_2935_: *mut LeanObject,
    mut v_target_2936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    v___x_2937_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5___redArg(v_i_2934_, v_source_2935_, v_target_2936_);
    return v___x_2937_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2938_: *mut LeanObject,
    mut v_x_2939_: *mut LeanObject,
    mut v_x_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    v___x_2941_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go_spec__2_spec__4_spec__5_spec__6___redArg(v_x_2939_, v_x_2940_);
    return v___x_2941_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0()
-> *mut LeanObject {
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    v___x_2942_ = lean_box(0);
    v___x_2943_ = lean_unsigned_to_nat(16);
    v___x_2944_ = lean_mk_array(v___x_2943_, v___x_2942_);
    return v___x_2944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1()
-> *mut LeanObject {
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    v___x_2945_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__0);
    v___x_2946_ = lean_unsigned_to_nat(0);
    v___x_2947_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2947_, 0, v___x_2946_);
    lean_ctor_set(v___x_2947_, 1, v___x_2945_);
    return v___x_2947_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3()
-> *mut LeanObject {
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    v___x_2950_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__2;
    v___x_2951_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__1);
    v___x_2952_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2952_, 0, v___x_2951_);
    lean_ctor_set(v___x_2952_, 1, v___x_2950_);
    lean_ctor_set(v___x_2952_, 2, v___x_2950_);
    lean_ctor_set(v___x_2952_, 3, v___x_2950_);
    return v___x_2952_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(
    mut v_lhs_2960_: *mut LeanObject,
    mut v_rhs_2961_: *mut LeanObject,
    mut v_a_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v_val_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2987_: u8 = 0;
    let mut v_snd_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v_varTypes_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhss_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhss_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut v_a_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_a_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_a_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v_a_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3069_: u8 = 0;
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2973_ = l_Lean_Meta_Sym_shareCommon___redArg(v_lhs_2960_, v_a_2967_);
                if lean_obj_tag(v___x_2973_) == 0 {
                    v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
                    lean_inc(v_a_2974_);
                    lean_dec_ref_known(v___x_2973_, 1);
                    v___x_2975_ = l_Lean_Meta_Sym_shareCommon___redArg(v_rhs_2961_, v_a_2967_);
                    if lean_obj_tag(v___x_2975_) == 0 {
                        v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
                        lean_inc(v_a_2976_);
                        lean_dec_ref_known(v___x_2975_, 1);
                        v___x_2977_ = lean_unsigned_to_nat(0);
                        v___x_2978_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__3);
                        v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f_go(v_a_2974_, v_a_2976_, v___x_2977_, v___x_2978_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
                        if lean_obj_tag(v___x_2979_) == 0 {
                            v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
                            v_isSharedCheck_3049_ = (!lean_is_exclusive(v___x_2979_)) as u8;
                            if v_isSharedCheck_3049_ == 0 {
                                v___x_2982_ = v___x_2979_;
                                v_isShared_2983_ = v_isSharedCheck_3049_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2980_);
                                lean_dec(v___x_2979_);
                                v___x_2982_ = lean_box(0);
                                v_isShared_2983_ = v_isSharedCheck_3049_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3050_ = lean_ctor_get(v___x_2979_, 0);
                            v_isSharedCheck_3057_ = (!lean_is_exclusive(v___x_2979_)) as u8;
                            if v_isSharedCheck_3057_ == 0 {
                                v___x_3052_ = v___x_2979_;
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_3050_);
                                lean_dec(v___x_2979_);
                                v___x_3052_ = lean_box(0);
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2974_);
                        v_a_3058_ = lean_ctor_get(v___x_2975_, 0);
                        v_isSharedCheck_3065_ = (!lean_is_exclusive(v___x_2975_)) as u8;
                        if v_isSharedCheck_3065_ == 0 {
                            v___x_3060_ = v___x_2975_;
                            v_isShared_3061_ = v_isSharedCheck_3065_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_3058_);
                            lean_dec(v___x_2975_);
                            v___x_3060_ = lean_box(0);
                            v_isShared_3061_ = v_isSharedCheck_3065_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_2961_);
                    v_a_3066_ = lean_ctor_get(v___x_2973_, 0);
                    v_isSharedCheck_3073_ = (!lean_is_exclusive(v___x_2973_)) as u8;
                    if v_isSharedCheck_3073_ == 0 {
                        v___x_3068_ = v___x_2973_;
                        v_isShared_3069_ = v_isSharedCheck_3073_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3066_);
                        lean_dec(v___x_2973_);
                        v___x_3068_ = lean_box(0);
                        v_isShared_3069_ = v_isSharedCheck_3073_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2980_) == 1 {
                    v_val_2984_ = lean_ctor_get(v_a_2980_, 0);
                    v_isSharedCheck_3044_ = (!lean_is_exclusive(v_a_2980_)) as u8;
                    if v_isSharedCheck_3044_ == 0 {
                        v___x_2986_ = v_a_2980_;
                        v_isShared_2987_ = v_isSharedCheck_3044_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2984_);
                        lean_dec(v_a_2980_);
                        v___x_2986_ = lean_box(0);
                        v_isShared_2987_ = v_isSharedCheck_3044_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2980_);
                    v___x_3045_ = lean_box(0);
                    if v_isShared_2983_ == 0 {
                        lean_ctor_set(v___x_2982_, 0, v___x_3045_);
                        v___x_3047_ = v___x_2982_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
                        v___x_3047_ = v_reuseFailAlloc_3048_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_2988_ = lean_ctor_get(v_val_2984_, 1);
                v_fst_2989_ = lean_ctor_get(v_val_2984_, 0);
                v_isSharedCheck_3043_ = (!lean_is_exclusive(v_val_2984_)) as u8;
                if v_isSharedCheck_3043_ == 0 {
                    v___x_2991_ = v_val_2984_;
                    v_isShared_2992_ = v_isSharedCheck_3043_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_2988_);
                    lean_inc(v_fst_2989_);
                    lean_dec(v_val_2984_);
                    v___x_2991_ = lean_box(0);
                    v_isShared_2992_ = v_isSharedCheck_3043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_varTypes_2993_ = lean_ctor_get(v_snd_2988_, 1);
                lean_inc_ref(v_varTypes_2993_);
                v_lhss_2994_ = lean_ctor_get(v_snd_2988_, 2);
                lean_inc_ref(v_lhss_2994_);
                v_rhss_2995_ = lean_ctor_get(v_snd_2988_, 3);
                lean_inc_ref(v_rhss_2995_);
                lean_dec(v_snd_2988_);
                v___x_2996_ = lean_array_get_size(v_lhss_2994_);
                v___x_2997_ = lean_nat_dec_eq(v___x_2996_, v___x_2977_);
                if v___x_2997_ == 0 {
                    lean_del_object(v___x_2982_);
                    v___x_2998_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_mkLambdaWithBodyAndVarType(v_varTypes_2993_, v_fst_2989_);
                    lean_dec_ref(v_varTypes_2993_);
                    lean_inc(v_a_2971_);
                    lean_inc_ref(v_a_2970_);
                    lean_inc(v_a_2969_);
                    lean_inc_ref(v_a_2968_);
                    lean_inc_ref(v___x_2998_);
                    v___x_2999_ =
                        lean_infer_type(v___x_2998_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
                    if lean_obj_tag(v___x_2999_) == 0 {
                        v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
                        lean_inc_n(v_a_3000_, 2);
                        lean_dec_ref_known(v___x_2999_, 1);
                        v___x_3001_ = l_Lean_Meta_getLevel(
                            v_a_3000_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_,
                        );
                        if lean_obj_tag(v___x_3001_) == 0 {
                            v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
                            v_isSharedCheck_3022_ = (!lean_is_exclusive(v___x_3001_)) as u8;
                            if v_isSharedCheck_3022_ == 0 {
                                v___x_3004_ = v___x_3001_;
                                v_isShared_3005_ = v_isSharedCheck_3022_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3002_);
                                lean_dec(v___x_3001_);
                                v___x_3004_ = lean_box(0);
                                v_isShared_3005_ = v_isSharedCheck_3022_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3000_);
                            lean_dec_ref(v___x_2998_);
                            lean_dec_ref(v_rhss_2995_);
                            lean_dec_ref(v_lhss_2994_);
                            lean_del_object(v___x_2991_);
                            lean_del_object(v___x_2986_);
                            v_a_3023_ = lean_ctor_get(v___x_3001_, 0);
                            v_isSharedCheck_3030_ = (!lean_is_exclusive(v___x_3001_)) as u8;
                            if v_isSharedCheck_3030_ == 0 {
                                v___x_3025_ = v___x_3001_;
                                v_isShared_3026_ = v_isSharedCheck_3030_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3023_);
                                lean_dec(v___x_3001_);
                                v___x_3025_ = lean_box(0);
                                v_isShared_3026_ = v_isSharedCheck_3030_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2998_);
                        lean_dec_ref(v_rhss_2995_);
                        lean_dec_ref(v_lhss_2994_);
                        lean_del_object(v___x_2991_);
                        lean_del_object(v___x_2986_);
                        v_a_3031_ = lean_ctor_get(v___x_2999_, 0);
                        v_isSharedCheck_3038_ = (!lean_is_exclusive(v___x_2999_)) as u8;
                        if v_isSharedCheck_3038_ == 0 {
                            v___x_3033_ = v___x_2999_;
                            v_isShared_3034_ = v_isSharedCheck_3038_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3031_);
                            lean_dec(v___x_2999_);
                            v___x_3033_ = lean_box(0);
                            v_isShared_3034_ = v_isSharedCheck_3038_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhss_2995_);
                    lean_dec_ref(v_lhss_2994_);
                    lean_dec_ref(v_varTypes_2993_);
                    lean_del_object(v___x_2991_);
                    lean_dec(v_fst_2989_);
                    lean_del_object(v___x_2986_);
                    v___x_3039_ = lean_box(0);
                    if v_isShared_2983_ == 0 {
                        lean_ctor_set(v___x_2982_, 0, v___x_3039_);
                        v___x_3041_ = v___x_2982_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
                        v___x_3041_ = v_reuseFailAlloc_3042_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3006_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f___closed__7;
                v___x_3007_ = lean_box(0);
                v___x_3008_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3008_, 0, v_a_3002_);
                lean_ctor_set(v___x_3008_, 1, v___x_3007_);
                v___x_3009_ = l_Lean_Expr_const___override(v___x_3006_, v___x_3008_);
                v___x_3010_ = l_Lean_mkAppB(v___x_3009_, v_a_3000_, v___x_2998_);
                lean_inc_ref(v___x_3010_);
                v___x_3011_ = l_Lean_mkAppN(v___x_3010_, v_lhss_2994_);
                lean_dec_ref(v_lhss_2994_);
                v___x_3012_ = l_Lean_mkAppN(v___x_3010_, v_rhss_2995_);
                lean_dec_ref(v_rhss_2995_);
                if v_isShared_2992_ == 0 {
                    lean_ctor_set(v___x_2991_, 1, v___x_3012_);
                    lean_ctor_set(v___x_2991_, 0, v___x_3011_);
                    v___x_3014_ = v___x_2991_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3011_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3012_);
                    v___x_3014_ = v_reuseFailAlloc_3021_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2987_ == 0 {
                    lean_ctor_set(v___x_2986_, 0, v___x_3014_);
                    v___x_3016_ = v___x_2986_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3014_);
                    v___x_3016_ = v_reuseFailAlloc_3020_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3005_ == 0 {
                    lean_ctor_set(v___x_3004_, 0, v___x_3016_);
                    v___x_3018_ = v___x_3004_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
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
                    v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
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
                    v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
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
                    v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
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
                    v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
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
                    v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
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
    mut v_lhs_3074_: *mut LeanObject,
    mut v_rhs_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_a_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
    mut v_a_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3087_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3085_);
    lean_dec_ref(v_a_3084_);
    lean_dec(v_a_3083_);
    lean_dec_ref(v_a_3082_);
    lean_dec(v_a_3081_);
    lean_dec_ref(v_a_3080_);
    lean_dec(v_a_3079_);
    lean_dec_ref(v_a_3078_);
    lean_dec(v_a_3077_);
    lean_dec(v_a_3076_);
    return v_res_3087_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(
    mut v_msgData_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    v___x_3094_ = lean_st_ref_get(v___y_3092_);
    v_env_3095_ = lean_ctor_get(v___x_3094_, 0);
    lean_inc_ref(v_env_3095_);
    lean_dec(v___x_3094_);
    v___x_3096_ = lean_st_ref_get(v___y_3090_);
    v_mctx_3097_ = lean_ctor_get(v___x_3096_, 0);
    lean_inc_ref(v_mctx_3097_);
    lean_dec(v___x_3096_);
    v_lctx_3098_ = lean_ctor_get(v___y_3089_, 2);
    v_options_3099_ = lean_ctor_get(v___y_3091_, 2);
    lean_inc_ref(v_options_3099_);
    lean_inc_ref(v_lctx_3098_);
    v___x_3100_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3100_, 0, v_env_3095_);
    lean_ctor_set(v___x_3100_, 1, v_mctx_3097_);
    lean_ctor_set(v___x_3100_, 2, v_lctx_3098_);
    lean_ctor_set(v___x_3100_, 3, v_options_3099_);
    v___x_3101_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3101_, 0, v___x_3100_);
    lean_ctor_set(v___x_3101_, 1, v_msgData_3088_);
    v___x_3102_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3102_, 0, v___x_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0___boxed(
    mut v_msgData_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3109_: *mut LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msgData_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
    lean_dec(v___y_3107_);
    lean_dec_ref(v___y_3106_);
    lean_dec(v___y_3105_);
    lean_dec_ref(v___y_3104_);
    return v_res_3109_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: f64 = 0.0;
    v___x_3110_ = lean_unsigned_to_nat(0);
    v___x_3111_ = lean_float_of_nat(v___x_3110_);
    return v___x_3111_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(
    mut v_cls_3115_: *mut LeanObject,
    mut v_msg_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3140_: u8 = 0;
    let mut v_tid_3141_: u64 = 0;
    let mut v_traces_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: f64 = 0.0;
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3166_: u8 = 0;
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3122_ = lean_ctor_get(v___y_3119_, 5);
                v___x_3123_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0_spec__0(v_msg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
                v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
                v_isSharedCheck_3168_ = (!lean_is_exclusive(v___x_3123_)) as u8;
                if v_isSharedCheck_3168_ == 0 {
                    v___x_3126_ = v___x_3123_;
                    v_isShared_3127_ = v_isSharedCheck_3168_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3124_);
                    lean_dec(v___x_3123_);
                    v___x_3126_ = lean_box(0);
                    v_isShared_3127_ = v_isSharedCheck_3168_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3128_ = lean_st_ref_take(v___y_3120_);
                v_traceState_3129_ = lean_ctor_get(v___x_3128_, 4);
                v_env_3130_ = lean_ctor_get(v___x_3128_, 0);
                v_nextMacroScope_3131_ = lean_ctor_get(v___x_3128_, 1);
                v_ngen_3132_ = lean_ctor_get(v___x_3128_, 2);
                v_auxDeclNGen_3133_ = lean_ctor_get(v___x_3128_, 3);
                v_cache_3134_ = lean_ctor_get(v___x_3128_, 5);
                v_messages_3135_ = lean_ctor_get(v___x_3128_, 6);
                v_infoState_3136_ = lean_ctor_get(v___x_3128_, 7);
                v_snapshotTasks_3137_ = lean_ctor_get(v___x_3128_, 8);
                v_isSharedCheck_3167_ = (!lean_is_exclusive(v___x_3128_)) as u8;
                if v_isSharedCheck_3167_ == 0 {
                    v___x_3139_ = v___x_3128_;
                    v_isShared_3140_ = v_isSharedCheck_3167_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3137_);
                    lean_inc(v_infoState_3136_);
                    lean_inc(v_messages_3135_);
                    lean_inc(v_cache_3134_);
                    lean_inc(v_traceState_3129_);
                    lean_inc(v_auxDeclNGen_3133_);
                    lean_inc(v_ngen_3132_);
                    lean_inc(v_nextMacroScope_3131_);
                    lean_inc(v_env_3130_);
                    lean_dec(v___x_3128_);
                    v___x_3139_ = lean_box(0);
                    v_isShared_3140_ = v_isSharedCheck_3167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3141_ = lean_ctor_get_uint64(
                    v_traceState_3129_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3142_ = lean_ctor_get(v_traceState_3129_, 0);
                v_isSharedCheck_3166_ = (!lean_is_exclusive(v_traceState_3129_)) as u8;
                if v_isSharedCheck_3166_ == 0 {
                    v___x_3144_ = v_traceState_3129_;
                    v_isShared_3145_ = v_isSharedCheck_3166_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3142_);
                    lean_dec(v_traceState_3129_);
                    v___x_3144_ = lean_box(0);
                    v_isShared_3145_ = v_isSharedCheck_3166_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3146_ = lean_box(0);
                v___x_3147_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__0);
                v___x_3148_ = 0;
                v___x_3149_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__1;
                v___x_3150_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3150_, 0, v_cls_3115_);
                lean_ctor_set(v___x_3150_, 1, v___x_3146_);
                lean_ctor_set(v___x_3150_, 2, v___x_3149_);
                lean_ctor_set_float(
                    v___x_3150_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3147_,
                );
                lean_ctor_set_float(
                    v___x_3150_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3147_,
                );
                lean_ctor_set_uint8(
                    v___x_3150_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3148_,
                );
                v___x_3151_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg___closed__2;
                v___x_3152_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3152_, 0, v___x_3150_);
                lean_ctor_set(v___x_3152_, 1, v_a_3124_);
                lean_ctor_set(v___x_3152_, 2, v___x_3151_);
                lean_inc(v_ref_3122_);
                v___x_3153_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3153_, 0, v_ref_3122_);
                lean_ctor_set(v___x_3153_, 1, v___x_3152_);
                v___x_3154_ = l_Lean_PersistentArray_push___redArg(v_traces_3142_, v___x_3153_);
                if v_isShared_3145_ == 0 {
                    lean_ctor_set(v___x_3144_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3144_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3154_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3165_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3141_,
                    );
                    v___x_3156_ = v_reuseFailAlloc_3165_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3140_ == 0 {
                    lean_ctor_set(v___x_3139_, 4, v___x_3156_);
                    v___x_3158_ = v___x_3139_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_env_3130_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_nextMacroScope_3131_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_ngen_3132_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_auxDeclNGen_3133_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 4, v___x_3156_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 5, v_cache_3134_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 6, v_messages_3135_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 7, v_infoState_3136_);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 8, v_snapshotTasks_3137_);
                    v___x_3158_ = v_reuseFailAlloc_3164_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3159_ = lean_st_ref_set(v___y_3120_, v___x_3158_);
                v___x_3160_ = lean_box(0);
                if v_isShared_3127_ == 0 {
                    lean_ctor_set(v___x_3126_, 0, v___x_3160_);
                    v___x_3162_ = v___x_3126_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
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
    mut v_cls_3169_: *mut LeanObject,
    mut v_msg_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3176_: *mut LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_3169_, v_msg_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
    lean_dec(v___y_3174_);
    lean_dec_ref(v___y_3173_);
    lean_dec(v___y_3172_);
    lean_dec_ref(v___y_3171_);
    return v_res_3176_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6()
-> *mut LeanObject {
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    v___x_3187_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
    v___x_3188_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__5;
    v___x_3189_ = l_Lean_Name_append(v___x_3188_, v___x_3187_);
    return v___x_3189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8()
-> *mut LeanObject {
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    v___x_3191_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__7;
    v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
    return v___x_3192_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10()
-> *mut LeanObject {
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    v___x_3194_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__9;
    v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
    return v___x_3195_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12()
-> *mut LeanObject {
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    v___x_3197_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__11;
    v___x_3198_ = l_Lean_stringToMessageData(v___x_3197_);
    return v___x_3198_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(
    mut v_lhs_u2080_3199_: *mut LeanObject,
    mut v_rhs_u2080_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
    mut v_a_3203_: *mut LeanObject,
    mut v_a_3204_: *mut LeanObject,
    mut v_a_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
    mut v_a_3207_: *mut LeanObject,
    mut v_a_3208_: *mut LeanObject,
    mut v_a_3209_: *mut LeanObject,
    mut v_a_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v_val_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v_fst_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___y_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3246_: u8 = 0;
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_a_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v_a_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_a_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_options_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3306_: u8 = 0;
    let mut v_inheritedTraceOptions_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut v_reuseFailAlloc_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v_a_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3212_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_abstractGroundMismatches_x3f(v_lhs_u2080_3199_, v_rhs_u2080_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
                if lean_obj_tag(v___x_3212_) == 0 {
                    v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
                    v_isSharedCheck_3337_ = (!lean_is_exclusive(v___x_3212_)) as u8;
                    if v_isSharedCheck_3337_ == 0 {
                        v___x_3215_ = v___x_3212_;
                        v_isShared_3216_ = v_isSharedCheck_3337_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3213_);
                        lean_dec(v___x_3212_);
                        v___x_3215_ = lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3337_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3338_ = lean_ctor_get(v___x_3212_, 0);
                    v_isSharedCheck_3345_ = (!lean_is_exclusive(v___x_3212_)) as u8;
                    if v_isSharedCheck_3345_ == 0 {
                        v___x_3340_ = v___x_3212_;
                        v_isShared_3341_ = v_isSharedCheck_3345_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_3338_);
                        lean_dec(v___x_3212_);
                        v___x_3340_ = lean_box(0);
                        v_isShared_3341_ = v_isSharedCheck_3345_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3213_) == 1 {
                    lean_del_object(v___x_3215_);
                    v_val_3217_ = lean_ctor_get(v_a_3213_, 0);
                    v_isSharedCheck_3332_ = (!lean_is_exclusive(v_a_3213_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3219_ = v_a_3213_;
                        v_isShared_3220_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3217_);
                        lean_dec(v_a_3213_);
                        v___x_3219_ = lean_box(0);
                        v_isShared_3220_ = v_isSharedCheck_3332_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3213_);
                    v___x_3333_ = lean_box(0);
                    if v_isShared_3216_ == 0 {
                        lean_ctor_set(v___x_3215_, 0, v___x_3333_);
                        v___x_3335_ = v___x_3215_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
                        v___x_3335_ = v_reuseFailAlloc_3336_;
                        state = 23;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3221_ = lean_ctor_get(v_val_3217_, 0);
                v_snd_3222_ = lean_ctor_get(v_val_3217_, 1);
                v_isSharedCheck_3331_ = (!lean_is_exclusive(v_val_3217_)) as u8;
                if v_isSharedCheck_3331_ == 0 {
                    v___x_3224_ = v_val_3217_;
                    v_isShared_3225_ = v_isSharedCheck_3331_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3222_);
                    lean_inc(v_fst_3221_);
                    lean_dec(v_val_3217_);
                    v___x_3224_ = lean_box(0);
                    v_isShared_3225_ = v_isSharedCheck_3331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_options_3305_ = lean_ctor_get(v_a_3209_, 2);
                v_hasTrace_3306_ = lean_ctor_get_uint8(
                    v_options_3305_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3306_ == 0 {
                    lean_del_object(v___x_3224_);
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
                    v_inheritedTraceOptions_3307_ = lean_ctor_get(v_a_3209_, 13);
                    v___x_3308_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__3;
                    v___x_3309_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
                    v___x_3310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3307_,
                        v_options_3305_,
                        v___x_3309_,
                    );
                    if v___x_3310_ == 0 {
                        lean_del_object(v___x_3224_);
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
                        v___x_3311_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__8);
                        lean_inc(v_fst_3221_);
                        v___x_3312_ = l_Lean_MessageData_ofExpr(v_fst_3221_);
                        if v_isShared_3225_ == 0 {
                            lean_ctor_set_tag(v___x_3224_, 7);
                            lean_ctor_set(v___x_3224_, 1, v___x_3312_);
                            lean_ctor_set(v___x_3224_, 0, v___x_3311_);
                            v___x_3314_ = v___x_3224_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_3330_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3311_);
                            lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___x_3312_);
                            v___x_3314_ = v_reuseFailAlloc_3330_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_3237_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_fst_3221_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
                if lean_obj_tag(v___x_3237_) == 0 {
                    v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
                    lean_inc(v_a_3238_);
                    lean_dec_ref_known(v___x_3237_, 1);
                    v___x_3239_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_snd_3222_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
                    if lean_obj_tag(v___x_3239_) == 0 {
                        v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
                        lean_inc(v_a_3240_);
                        lean_dec_ref_known(v___x_3239_, 1);
                        lean_inc(v___y_3236_);
                        lean_inc_ref(v___y_3235_);
                        lean_inc(v___y_3234_);
                        lean_inc_ref(v___y_3233_);
                        lean_inc(v___y_3232_);
                        lean_inc_ref(v___y_3231_);
                        lean_inc(v___y_3230_);
                        lean_inc_ref(v___y_3229_);
                        lean_inc(v___y_3228_);
                        lean_inc(v___y_3227_);
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
                        if lean_obj_tag(v___x_3241_) == 0 {
                            lean_dec_ref_known(v___x_3241_, 1);
                            v___x_3242_ =
                                l_Lean_Meta_Grind_isEqv___redArg(v_a_3238_, v_a_3240_, v___y_3227_);
                            if lean_obj_tag(v___x_3242_) == 0 {
                                v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
                                v_isSharedCheck_3272_ = (!lean_is_exclusive(v___x_3242_)) as u8;
                                if v_isSharedCheck_3272_ == 0 {
                                    v___x_3245_ = v___x_3242_;
                                    v_isShared_3246_ = v_isSharedCheck_3272_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_3243_);
                                    lean_dec(v___x_3242_);
                                    v___x_3245_ = lean_box(0);
                                    v_isShared_3246_ = v_isSharedCheck_3272_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3240_);
                                lean_dec(v_a_3238_);
                                lean_del_object(v___x_3219_);
                                v_a_3273_ = lean_ctor_get(v___x_3242_, 0);
                                v_isSharedCheck_3280_ = (!lean_is_exclusive(v___x_3242_)) as u8;
                                if v_isSharedCheck_3280_ == 0 {
                                    v___x_3275_ = v___x_3242_;
                                    v_isShared_3276_ = v_isSharedCheck_3280_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_3273_);
                                    lean_dec(v___x_3242_);
                                    v___x_3275_ = lean_box(0);
                                    v_isShared_3276_ = v_isSharedCheck_3280_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3240_);
                            lean_dec(v_a_3238_);
                            lean_del_object(v___x_3219_);
                            v_a_3281_ = lean_ctor_get(v___x_3241_, 0);
                            v_isSharedCheck_3288_ = (!lean_is_exclusive(v___x_3241_)) as u8;
                            if v_isSharedCheck_3288_ == 0 {
                                v___x_3283_ = v___x_3241_;
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_3281_);
                                lean_dec(v___x_3241_);
                                v___x_3283_ = lean_box(0);
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3238_);
                        lean_del_object(v___x_3219_);
                        v_a_3289_ = lean_ctor_get(v___x_3239_, 0);
                        v_isSharedCheck_3296_ = (!lean_is_exclusive(v___x_3239_)) as u8;
                        if v_isSharedCheck_3296_ == 0 {
                            v___x_3291_ = v___x_3239_;
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_3289_);
                            lean_dec(v___x_3239_);
                            v___x_3291_ = lean_box(0);
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_3222_);
                    lean_del_object(v___x_3219_);
                    v_a_3297_ = lean_ctor_get(v___x_3237_, 0);
                    v_isSharedCheck_3304_ = (!lean_is_exclusive(v___x_3237_)) as u8;
                    if v_isSharedCheck_3304_ == 0 {
                        v___x_3299_ = v___x_3237_;
                        v_isShared_3300_ = v_isSharedCheck_3304_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3297_);
                        lean_dec(v___x_3237_);
                        v___x_3299_ = lean_box(0);
                        v_isShared_3300_ = v_isSharedCheck_3304_;
                        state = 18;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3247_ = (lean_unbox(v_a_3243_) as u8);
                lean_dec(v_a_3243_);
                if v___x_3247_ == 0 {
                    lean_dec(v_a_3240_);
                    lean_dec(v_a_3238_);
                    lean_del_object(v___x_3219_);
                    v___x_3248_ = lean_box(0);
                    if v_isShared_3246_ == 0 {
                        lean_ctor_set(v___x_3245_, 0, v___x_3248_);
                        v___x_3250_ = v___x_3245_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                        v___x_3250_ = v_reuseFailAlloc_3251_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3245_);
                    lean_inc(v___y_3236_);
                    lean_inc_ref(v___y_3235_);
                    lean_inc(v___y_3234_);
                    lean_inc_ref(v___y_3233_);
                    lean_inc(v___y_3232_);
                    lean_inc_ref(v___y_3231_);
                    lean_inc(v___y_3230_);
                    lean_inc_ref(v___y_3229_);
                    lean_inc(v___y_3228_);
                    lean_inc(v___y_3227_);
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
                    if lean_obj_tag(v___x_3252_) == 0 {
                        v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
                        v_isSharedCheck_3263_ = (!lean_is_exclusive(v___x_3252_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v___x_3255_ = v___x_3252_;
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3253_);
                            lean_dec(v___x_3252_);
                            v___x_3255_ = lean_box(0);
                            v_isShared_3256_ = v_isSharedCheck_3263_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3219_);
                        v_a_3264_ = lean_ctor_get(v___x_3252_, 0);
                        v_isSharedCheck_3271_ = (!lean_is_exclusive(v___x_3252_)) as u8;
                        if v_isSharedCheck_3271_ == 0 {
                            v___x_3266_ = v___x_3252_;
                            v_isShared_3267_ = v_isSharedCheck_3271_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3264_);
                            lean_dec(v___x_3252_);
                            v___x_3266_ = lean_box(0);
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
                    lean_ctor_set(v___x_3219_, 0, v_a_3253_);
                    v___x_3258_ = v___x_3219_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3253_);
                    v___x_3258_ = v_reuseFailAlloc_3262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3256_ == 0 {
                    lean_ctor_set(v___x_3255_, 0, v___x_3258_);
                    v___x_3260_ = v___x_3255_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
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
                    v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
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
                    v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
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
                    v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
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
                    v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
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
                    v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
                    v___x_3302_ = v_reuseFailAlloc_3303_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3302_;
            }
            20 => {
                v___x_3315_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
                v___x_3316_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3316_, 0, v___x_3314_);
                lean_ctor_set(v___x_3316_, 1, v___x_3315_);
                lean_inc(v_snd_3222_);
                v___x_3317_ = l_Lean_MessageData_ofExpr(v_snd_3222_);
                v___x_3318_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3318_, 0, v___x_3316_);
                lean_ctor_set(v___x_3318_, 1, v___x_3317_);
                v___x_3319_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
                v___x_3320_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3320_, 0, v___x_3318_);
                lean_ctor_set(v___x_3320_, 1, v___x_3319_);
                v___x_3321_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v___x_3308_, v___x_3320_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
                if lean_obj_tag(v___x_3321_) == 0 {
                    lean_dec_ref_known(v___x_3321_, 1);
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
                    lean_dec(v_snd_3222_);
                    lean_dec(v_fst_3221_);
                    lean_del_object(v___x_3219_);
                    v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
                    v_isSharedCheck_3329_ = (!lean_is_exclusive(v___x_3321_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3324_ = v___x_3321_;
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3322_);
                        lean_dec(v___x_3321_);
                        v___x_3324_ = lean_box(0);
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
                    v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
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
                    v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
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
    mut v_lhs_u2080_3346_: *mut LeanObject,
    mut v_rhs_u2080_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_a_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3359_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3357_);
    lean_dec_ref(v_a_3356_);
    lean_dec(v_a_3355_);
    lean_dec_ref(v_a_3354_);
    lean_dec(v_a_3353_);
    lean_dec_ref(v_a_3352_);
    lean_dec(v_a_3351_);
    lean_dec_ref(v_a_3350_);
    lean_dec(v_a_3349_);
    lean_dec(v_a_3348_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(
    mut v_cls_3360_: *mut LeanObject,
    mut v_msg_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    v___x_3373_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_3360_, v_msg_3361_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___boxed(
    mut v_cls_3374_: *mut LeanObject,
    mut v_msg_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0(v_cls_3374_, v_msg_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
    lean_dec(v___y_3385_);
    lean_dec_ref(v___y_3384_);
    lean_dec(v___y_3383_);
    lean_dec_ref(v___y_3382_);
    lean_dec(v___y_3381_);
    lean_dec_ref(v___y_3380_);
    lean_dec(v___y_3379_);
    lean_dec_ref(v___y_3378_);
    lean_dec(v___y_3377_);
    lean_dec(v___y_3376_);
    return v_res_3387_;
}
pub unsafe fn l_Lean_Meta_Grind_proveEq_x3f___lam__0(
    mut v_lhs_3388_: *mut LeanObject,
    mut v_rhs_3389_: *mut LeanObject,
    mut v_abstract_3390_: u8,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v_a_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_a_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v_a_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v_a_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_3388_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
                if lean_obj_tag(v___x_3402_) == 0 {
                    v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
                    lean_inc(v_a_3403_);
                    lean_dec_ref_known(v___x_3402_, 1);
                    v___x_3404_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_3389_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
                    if lean_obj_tag(v___x_3404_) == 0 {
                        v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
                        lean_inc(v_a_3405_);
                        lean_dec_ref_known(v___x_3404_, 1);
                        lean_inc(v___y_3400_);
                        lean_inc_ref(v___y_3399_);
                        lean_inc(v___y_3398_);
                        lean_inc_ref(v___y_3397_);
                        lean_inc(v___y_3396_);
                        lean_inc_ref(v___y_3395_);
                        lean_inc(v___y_3394_);
                        lean_inc_ref(v___y_3393_);
                        lean_inc(v___y_3392_);
                        lean_inc(v___y_3391_);
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
                        if lean_obj_tag(v___x_3406_) == 0 {
                            lean_dec_ref_known(v___x_3406_, 1);
                            v___x_3407_ =
                                l_Lean_Meta_Grind_isEqv___redArg(v_a_3403_, v_a_3405_, v___y_3391_);
                            if lean_obj_tag(v___x_3407_) == 0 {
                                v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
                                v_isSharedCheck_3436_ = (!lean_is_exclusive(v___x_3407_)) as u8;
                                if v_isSharedCheck_3436_ == 0 {
                                    v___x_3410_ = v___x_3407_;
                                    v_isShared_3411_ = v_isSharedCheck_3436_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_3408_);
                                    lean_dec(v___x_3407_);
                                    v___x_3410_ = lean_box(0);
                                    v_isShared_3411_ = v_isSharedCheck_3436_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3405_);
                                lean_dec(v_a_3403_);
                                v_a_3437_ = lean_ctor_get(v___x_3407_, 0);
                                v_isSharedCheck_3444_ = (!lean_is_exclusive(v___x_3407_)) as u8;
                                if v_isSharedCheck_3444_ == 0 {
                                    v___x_3439_ = v___x_3407_;
                                    v_isShared_3440_ = v_isSharedCheck_3444_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3437_);
                                    lean_dec(v___x_3407_);
                                    v___x_3439_ = lean_box(0);
                                    v_isShared_3440_ = v_isSharedCheck_3444_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3405_);
                            lean_dec(v_a_3403_);
                            v_a_3445_ = lean_ctor_get(v___x_3406_, 0);
                            v_isSharedCheck_3452_ = (!lean_is_exclusive(v___x_3406_)) as u8;
                            if v_isSharedCheck_3452_ == 0 {
                                v___x_3447_ = v___x_3406_;
                                v_isShared_3448_ = v_isSharedCheck_3452_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3445_);
                                lean_dec(v___x_3406_);
                                v___x_3447_ = lean_box(0);
                                v_isShared_3448_ = v_isSharedCheck_3452_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3403_);
                        v_a_3453_ = lean_ctor_get(v___x_3404_, 0);
                        v_isSharedCheck_3460_ = (!lean_is_exclusive(v___x_3404_)) as u8;
                        if v_isSharedCheck_3460_ == 0 {
                            v___x_3455_ = v___x_3404_;
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3453_);
                            lean_dec(v___x_3404_);
                            v___x_3455_ = lean_box(0);
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_3389_);
                    v_a_3461_ = lean_ctor_get(v___x_3402_, 0);
                    v_isSharedCheck_3468_ = (!lean_is_exclusive(v___x_3402_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3463_ = v___x_3402_;
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3461_);
                        lean_dec(v___x_3402_);
                        v___x_3463_ = lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3412_ = (lean_unbox(v_a_3408_) as u8);
                lean_dec(v_a_3408_);
                if v___x_3412_ == 0 {
                    if v_abstract_3390_ == 0 {
                        lean_dec(v_a_3405_);
                        lean_dec(v_a_3403_);
                        v___x_3413_ = lean_box(0);
                        if v_isShared_3411_ == 0 {
                            lean_ctor_set(v___x_3410_, 0, v___x_3413_);
                            v___x_3415_ = v___x_3410_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
                            v___x_3415_ = v_reuseFailAlloc_3416_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3410_);
                        v___x_3417_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract(v_a_3403_, v_a_3405_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
                        return v___x_3417_;
                    }
                } else {
                    lean_del_object(v___x_3410_);
                    lean_inc(v___y_3400_);
                    lean_inc_ref(v___y_3399_);
                    lean_inc(v___y_3398_);
                    lean_inc_ref(v___y_3397_);
                    lean_inc(v___y_3396_);
                    lean_inc_ref(v___y_3395_);
                    lean_inc(v___y_3394_);
                    lean_inc_ref(v___y_3393_);
                    lean_inc(v___y_3392_);
                    lean_inc(v___y_3391_);
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
                    if lean_obj_tag(v___x_3418_) == 0 {
                        v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
                        v_isSharedCheck_3427_ = (!lean_is_exclusive(v___x_3418_)) as u8;
                        if v_isSharedCheck_3427_ == 0 {
                            v___x_3421_ = v___x_3418_;
                            v_isShared_3422_ = v_isSharedCheck_3427_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3419_);
                            lean_dec(v___x_3418_);
                            v___x_3421_ = lean_box(0);
                            v_isShared_3422_ = v_isSharedCheck_3427_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3428_ = lean_ctor_get(v___x_3418_, 0);
                        v_isSharedCheck_3435_ = (!lean_is_exclusive(v___x_3418_)) as u8;
                        if v_isSharedCheck_3435_ == 0 {
                            v___x_3430_ = v___x_3418_;
                            v_isShared_3431_ = v_isSharedCheck_3435_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3428_);
                            lean_dec(v___x_3418_);
                            v___x_3430_ = lean_box(0);
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
                v___x_3423_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3423_, 0, v_a_3419_);
                if v_isShared_3422_ == 0 {
                    lean_ctor_set(v___x_3421_, 0, v___x_3423_);
                    v___x_3425_ = v___x_3421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
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
                    v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
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
                    v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
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
                    v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
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
                    v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
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
                    v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
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
    mut v_lhs_3469_: *mut LeanObject,
    mut v_rhs_3470_: *mut LeanObject,
    mut v_abstract_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_abstract_boxed_3483_: u8 = 0;
    let mut v_res_3484_: *mut LeanObject = core::ptr::null_mut();
    v_abstract_boxed_3483_ = (lean_unbox(v_abstract_3471_) as u8);
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
    lean_dec(v___y_3481_);
    lean_dec_ref(v___y_3480_);
    lean_dec(v___y_3479_);
    lean_dec_ref(v___y_3478_);
    lean_dec(v___y_3477_);
    lean_dec_ref(v___y_3476_);
    lean_dec(v___y_3475_);
    lean_dec_ref(v___y_3474_);
    lean_dec(v___y_3473_);
    lean_dec(v___y_3472_);
    return v_res_3484_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1() -> *mut LeanObject {
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3486_ = l_Lean_Meta_Grind_proveEq_x3f___closed__0;
    v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_Meta_Grind_proveEq_x3f(
    mut v_lhs_3488_: *mut LeanObject,
    mut v_rhs_3489_: *mut LeanObject,
    mut v_abstract_3490_: u8,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3504_: u8 = 0;
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut v_a_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3547_: u8 = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut v_a_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_a_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut v___y_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3594_: u8 = 0;
    let mut v_a_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3598_: u8 = 0;
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_cls_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3502_ = lean_ctor_get(v_a_3499_, 2);
                v_inheritedTraceOptions_3503_ = lean_ctor_get(v_a_3499_, 13);
                v_hasTrace_3504_ = lean_ctor_get_uint8(
                    v_options_3502_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_3505_ = lean_box((v_abstract_3490_) as usize);
                lean_inc_ref(v_rhs_3489_);
                lean_inc_ref(v_lhs_3488_);
                v___f_3506_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_proveEq_x3f___lam__0___boxed as *mut core::ffi::c_void,
                    14,
                    3,
                );
                lean_closure_set(v___f_3506_, 0, v_lhs_3488_);
                lean_closure_set(v___f_3506_, 1, v_rhs_3489_);
                lean_closure_set(v___f_3506_, 2, v___x_3505_);
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
                    v___x_3604_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__6);
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
                        v___x_3606_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_proveEq_x3f___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_proveEq_x3f___closed__1_once),
                            _init_l_Lean_Meta_Grind_proveEq_x3f___closed__1,
                        );
                        lean_inc_ref(v_lhs_3488_);
                        v___x_3607_ = l_Lean_MessageData_ofExpr(v_lhs_3488_);
                        v___x_3608_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3608_, 0, v___x_3606_);
                        lean_ctor_set(v___x_3608_, 1, v___x_3607_);
                        v___x_3609_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__10);
                        v___x_3610_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3610_, 0, v___x_3608_);
                        lean_ctor_set(v___x_3610_, 1, v___x_3609_);
                        lean_inc_ref(v_rhs_3489_);
                        v___x_3611_ = l_Lean_MessageData_ofExpr(v_rhs_3489_);
                        v___x_3612_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                        lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                        v___x_3613_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___closed__12);
                        v___x_3614_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3614_, 0, v___x_3612_);
                        lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                        v___x_3615_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract_spec__0___redArg(v_cls_3603_, v___x_3614_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
                        if lean_obj_tag(v___x_3615_) == 0 {
                            lean_dec_ref_known(v___x_3615_, 1);
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
                            lean_dec_ref(v___f_3506_);
                            lean_dec_ref(v_rhs_3489_);
                            lean_dec_ref(v_lhs_3488_);
                            v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
                            v_isSharedCheck_3623_ = (!lean_is_exclusive(v___x_3615_)) as u8;
                            if v_isSharedCheck_3623_ == 0 {
                                v___x_3618_ = v___x_3615_;
                                v_isShared_3619_ = v_isSharedCheck_3623_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_3616_);
                                lean_dec(v___x_3615_);
                                v___x_3618_ = lean_box(0);
                                v_isShared_3619_ = v_isSharedCheck_3623_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3518_) == 0 {
                    v_a_3519_ = lean_ctor_get(v___y_3518_, 0);
                    lean_inc(v_a_3519_);
                    lean_dec_ref_known(v___y_3518_, 1);
                    v___x_3520_ = (lean_unbox(v_a_3519_) as u8);
                    lean_dec(v_a_3519_);
                    if v___x_3520_ == 0 {
                        lean_dec_ref(v_rhs_3489_);
                        lean_dec_ref(v_lhs_3488_);
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
                        lean_dec_ref(v___f_3506_);
                        v___x_3522_ =
                            l_Lean_Meta_Grind_isEqv___redArg(v_lhs_3488_, v_rhs_3489_, v___y_3516_);
                        if lean_obj_tag(v___x_3522_) == 0 {
                            v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
                            v_isSharedCheck_3552_ = (!lean_is_exclusive(v___x_3522_)) as u8;
                            if v_isSharedCheck_3552_ == 0 {
                                v___x_3525_ = v___x_3522_;
                                v_isShared_3526_ = v_isSharedCheck_3552_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3523_);
                                lean_dec(v___x_3522_);
                                v___x_3525_ = lean_box(0);
                                v_isShared_3526_ = v_isSharedCheck_3552_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_rhs_3489_);
                            lean_dec_ref(v_lhs_3488_);
                            v_a_3553_ = lean_ctor_get(v___x_3522_, 0);
                            v_isSharedCheck_3560_ = (!lean_is_exclusive(v___x_3522_)) as u8;
                            if v_isSharedCheck_3560_ == 0 {
                                v___x_3555_ = v___x_3522_;
                                v_isShared_3556_ = v_isSharedCheck_3560_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3553_);
                                lean_dec(v___x_3522_);
                                v___x_3555_ = lean_box(0);
                                v_isShared_3556_ = v_isSharedCheck_3560_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___f_3506_);
                    lean_dec_ref(v_rhs_3489_);
                    lean_dec_ref(v_lhs_3488_);
                    v_a_3561_ = lean_ctor_get(v___y_3518_, 0);
                    v_isSharedCheck_3568_ = (!lean_is_exclusive(v___y_3518_)) as u8;
                    if v_isSharedCheck_3568_ == 0 {
                        v___x_3563_ = v___y_3518_;
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3561_);
                        lean_dec(v___y_3518_);
                        v___x_3563_ = lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3527_ = (lean_unbox(v_a_3523_) as u8);
                lean_dec(v_a_3523_);
                if v___x_3527_ == 0 {
                    if v_abstract_3490_ == 0 {
                        lean_dec_ref(v_rhs_3489_);
                        lean_dec_ref(v_lhs_3488_);
                        v___x_3528_ = lean_box(0);
                        if v_isShared_3526_ == 0 {
                            lean_ctor_set(v___x_3525_, 0, v___x_3528_);
                            v___x_3530_ = v___x_3525_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
                            v___x_3530_ = v_reuseFailAlloc_3531_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3525_);
                        v___x_3532_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_proveEq_x3f_tryAbstract___boxed as *mut core::ffi::c_void, 13, 2);
                        lean_closure_set(v___x_3532_, 0, v_lhs_3488_);
                        lean_closure_set(v___x_3532_, 1, v_rhs_3489_);
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
                    lean_del_object(v___x_3525_);
                    lean_inc(v___y_3514_);
                    lean_inc_ref(v___y_3512_);
                    lean_inc(v___y_3508_);
                    lean_inc_ref(v___y_3517_);
                    lean_inc(v___y_3509_);
                    lean_inc_ref(v___y_3515_);
                    lean_inc(v___y_3510_);
                    lean_inc_ref(v___y_3511_);
                    lean_inc(v___y_3513_);
                    lean_inc(v___y_3516_);
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
                    if lean_obj_tag(v___x_3534_) == 0 {
                        v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
                        v_isSharedCheck_3543_ = (!lean_is_exclusive(v___x_3534_)) as u8;
                        if v_isSharedCheck_3543_ == 0 {
                            v___x_3537_ = v___x_3534_;
                            v_isShared_3538_ = v_isSharedCheck_3543_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3535_);
                            lean_dec(v___x_3534_);
                            v___x_3537_ = lean_box(0);
                            v_isShared_3538_ = v_isSharedCheck_3543_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3544_ = lean_ctor_get(v___x_3534_, 0);
                        v_isSharedCheck_3551_ = (!lean_is_exclusive(v___x_3534_)) as u8;
                        if v_isSharedCheck_3551_ == 0 {
                            v___x_3546_ = v___x_3534_;
                            v_isShared_3547_ = v_isSharedCheck_3551_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3544_);
                            lean_dec(v___x_3534_);
                            v___x_3546_ = lean_box(0);
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
                v___x_3539_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3539_, 0, v_a_3535_);
                if v_isShared_3538_ == 0 {
                    lean_ctor_set(v___x_3537_, 0, v___x_3539_);
                    v___x_3541_ = v___x_3537_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
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
                    v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
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
                    v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
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
                    v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
                    v___x_3566_ = v_reuseFailAlloc_3567_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3566_;
            }
            12 => {
                lean_inc_ref(v_rhs_3489_);
                lean_inc_ref(v_lhs_3488_);
                v___x_3580_ = l_Lean_Meta_Grind_hasSameType(
                    v_lhs_3488_,
                    v_rhs_3489_,
                    v___y_3576_,
                    v___y_3577_,
                    v___y_3578_,
                    v___y_3579_,
                );
                if lean_obj_tag(v___x_3580_) == 0 {
                    v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
                    v_isSharedCheck_3594_ = (!lean_is_exclusive(v___x_3580_)) as u8;
                    if v_isSharedCheck_3594_ == 0 {
                        v___x_3583_ = v___x_3580_;
                        v_isShared_3584_ = v_isSharedCheck_3594_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3581_);
                        lean_dec(v___x_3580_);
                        v___x_3583_ = lean_box(0);
                        v_isShared_3584_ = v_isSharedCheck_3594_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_3506_);
                    lean_dec_ref(v_rhs_3489_);
                    lean_dec_ref(v_lhs_3488_);
                    v_a_3595_ = lean_ctor_get(v___x_3580_, 0);
                    v_isSharedCheck_3602_ = (!lean_is_exclusive(v___x_3580_)) as u8;
                    if v_isSharedCheck_3602_ == 0 {
                        v___x_3597_ = v___x_3580_;
                        v_isShared_3598_ = v_isSharedCheck_3602_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3595_);
                        lean_dec(v___x_3580_);
                        v___x_3597_ = lean_box(0);
                        v_isShared_3598_ = v_isSharedCheck_3602_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                v___x_3585_ = (lean_unbox(v_a_3581_) as u8);
                lean_dec(v_a_3581_);
                if v___x_3585_ == 0 {
                    lean_dec_ref(v___f_3506_);
                    lean_dec_ref(v_rhs_3489_);
                    lean_dec_ref(v_lhs_3488_);
                    v___x_3586_ = lean_box(0);
                    if v_isShared_3584_ == 0 {
                        lean_ctor_set(v___x_3583_, 0, v___x_3586_);
                        v___x_3588_ = v___x_3583_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
                        v___x_3588_ = v_reuseFailAlloc_3589_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3583_);
                    v___x_3590_ =
                        l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_3488_, v___y_3570_);
                    if lean_obj_tag(v___x_3590_) == 0 {
                        v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
                        lean_inc(v_a_3591_);
                        v___x_3592_ = (lean_unbox(v_a_3591_) as u8);
                        lean_dec(v_a_3591_);
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
                            lean_dec_ref_known(v___x_3590_, 1);
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
                    v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
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
                    v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
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
    mut v_lhs_3624_: *mut LeanObject,
    mut v_rhs_3625_: *mut LeanObject,
    mut v_abstract_3626_: *mut LeanObject,
    mut v_a_3627_: *mut LeanObject,
    mut v_a_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
    mut v_a_3632_: *mut LeanObject,
    mut v_a_3633_: *mut LeanObject,
    mut v_a_3634_: *mut LeanObject,
    mut v_a_3635_: *mut LeanObject,
    mut v_a_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_abstract_boxed_3638_: u8 = 0;
    let mut v_res_3639_: *mut LeanObject = core::ptr::null_mut();
    v_abstract_boxed_3638_ = (lean_unbox(v_abstract_3626_) as u8);
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
    lean_dec(v_a_3636_);
    lean_dec_ref(v_a_3635_);
    lean_dec(v_a_3634_);
    lean_dec_ref(v_a_3633_);
    lean_dec(v_a_3632_);
    lean_dec_ref(v_a_3631_);
    lean_dec(v_a_3630_);
    lean_dec_ref(v_a_3629_);
    lean_dec(v_a_3628_);
    lean_dec(v_a_3627_);
    return v_res_3639_;
}
pub unsafe fn l_Lean_Meta_Grind_proveHEq_x3f___lam__0(
    mut v_lhs_3640_: *mut LeanObject,
    mut v_rhs_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3662_: u8 = 0;
    let mut v___x_3663_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_a_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_a_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_a_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_a_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_a_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3653_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_lhs_3640_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
                if lean_obj_tag(v___x_3653_) == 0 {
                    v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
                    lean_inc(v_a_3654_);
                    lean_dec_ref_known(v___x_3653_, 1);
                    v___x_3655_ = l___private_Lean_Meta_Tactic_Grind_ProveEq_0__Lean_Meta_Grind_ensureInternalized(v_rhs_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
                    if lean_obj_tag(v___x_3655_) == 0 {
                        v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
                        lean_inc(v_a_3656_);
                        lean_dec_ref_known(v___x_3655_, 1);
                        lean_inc(v___y_3651_);
                        lean_inc_ref(v___y_3650_);
                        lean_inc(v___y_3649_);
                        lean_inc_ref(v___y_3648_);
                        lean_inc(v___y_3647_);
                        lean_inc_ref(v___y_3646_);
                        lean_inc(v___y_3645_);
                        lean_inc_ref(v___y_3644_);
                        lean_inc(v___y_3643_);
                        lean_inc(v___y_3642_);
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
                        if lean_obj_tag(v___x_3657_) == 0 {
                            lean_dec_ref_known(v___x_3657_, 1);
                            v___x_3658_ =
                                l_Lean_Meta_Grind_isEqv___redArg(v_a_3654_, v_a_3656_, v___y_3642_);
                            if lean_obj_tag(v___x_3658_) == 0 {
                                v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
                                v_isSharedCheck_3686_ = (!lean_is_exclusive(v___x_3658_)) as u8;
                                if v_isSharedCheck_3686_ == 0 {
                                    v___x_3661_ = v___x_3658_;
                                    v_isShared_3662_ = v_isSharedCheck_3686_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_3659_);
                                    lean_dec(v___x_3658_);
                                    v___x_3661_ = lean_box(0);
                                    v_isShared_3662_ = v_isSharedCheck_3686_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3656_);
                                lean_dec(v_a_3654_);
                                v_a_3687_ = lean_ctor_get(v___x_3658_, 0);
                                v_isSharedCheck_3694_ = (!lean_is_exclusive(v___x_3658_)) as u8;
                                if v_isSharedCheck_3694_ == 0 {
                                    v___x_3689_ = v___x_3658_;
                                    v_isShared_3690_ = v_isSharedCheck_3694_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3687_);
                                    lean_dec(v___x_3658_);
                                    v___x_3689_ = lean_box(0);
                                    v_isShared_3690_ = v_isSharedCheck_3694_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3656_);
                            lean_dec(v_a_3654_);
                            v_a_3695_ = lean_ctor_get(v___x_3657_, 0);
                            v_isSharedCheck_3702_ = (!lean_is_exclusive(v___x_3657_)) as u8;
                            if v_isSharedCheck_3702_ == 0 {
                                v___x_3697_ = v___x_3657_;
                                v_isShared_3698_ = v_isSharedCheck_3702_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3695_);
                                lean_dec(v___x_3657_);
                                v___x_3697_ = lean_box(0);
                                v_isShared_3698_ = v_isSharedCheck_3702_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3654_);
                        v_a_3703_ = lean_ctor_get(v___x_3655_, 0);
                        v_isSharedCheck_3710_ = (!lean_is_exclusive(v___x_3655_)) as u8;
                        if v_isSharedCheck_3710_ == 0 {
                            v___x_3705_ = v___x_3655_;
                            v_isShared_3706_ = v_isSharedCheck_3710_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3703_);
                            lean_dec(v___x_3655_);
                            v___x_3705_ = lean_box(0);
                            v_isShared_3706_ = v_isSharedCheck_3710_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_3641_);
                    v_a_3711_ = lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3718_ = (!lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3718_ == 0 {
                        v___x_3713_ = v___x_3653_;
                        v_isShared_3714_ = v_isSharedCheck_3718_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3711_);
                        lean_dec(v___x_3653_);
                        v___x_3713_ = lean_box(0);
                        v_isShared_3714_ = v_isSharedCheck_3718_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3663_ = (lean_unbox(v_a_3659_) as u8);
                lean_dec(v_a_3659_);
                if v___x_3663_ == 0 {
                    lean_dec(v_a_3656_);
                    lean_dec(v_a_3654_);
                    v___x_3664_ = lean_box(0);
                    if v_isShared_3662_ == 0 {
                        lean_ctor_set(v___x_3661_, 0, v___x_3664_);
                        v___x_3666_ = v___x_3661_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                        v___x_3666_ = v_reuseFailAlloc_3667_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3661_);
                    lean_inc(v___y_3651_);
                    lean_inc_ref(v___y_3650_);
                    lean_inc(v___y_3649_);
                    lean_inc_ref(v___y_3648_);
                    lean_inc(v___y_3647_);
                    lean_inc_ref(v___y_3646_);
                    lean_inc(v___y_3645_);
                    lean_inc_ref(v___y_3644_);
                    lean_inc(v___y_3643_);
                    lean_inc(v___y_3642_);
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
                    if lean_obj_tag(v___x_3668_) == 0 {
                        v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
                        v_isSharedCheck_3677_ = (!lean_is_exclusive(v___x_3668_)) as u8;
                        if v_isSharedCheck_3677_ == 0 {
                            v___x_3671_ = v___x_3668_;
                            v_isShared_3672_ = v_isSharedCheck_3677_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3669_);
                            lean_dec(v___x_3668_);
                            v___x_3671_ = lean_box(0);
                            v_isShared_3672_ = v_isSharedCheck_3677_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3678_ = lean_ctor_get(v___x_3668_, 0);
                        v_isSharedCheck_3685_ = (!lean_is_exclusive(v___x_3668_)) as u8;
                        if v_isSharedCheck_3685_ == 0 {
                            v___x_3680_ = v___x_3668_;
                            v_isShared_3681_ = v_isSharedCheck_3685_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3678_);
                            lean_dec(v___x_3668_);
                            v___x_3680_ = lean_box(0);
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
                v___x_3673_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3673_, 0, v_a_3669_);
                if v_isShared_3672_ == 0 {
                    lean_ctor_set(v___x_3671_, 0, v___x_3673_);
                    v___x_3675_ = v___x_3671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
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
                    v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
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
                    v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
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
                    v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
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
                    v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
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
                    v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
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
    mut v_lhs_3719_: *mut LeanObject,
    mut v_rhs_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
    mut v___y_3729_: *mut LeanObject,
    mut v___y_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3732_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3730_);
    lean_dec_ref(v___y_3729_);
    lean_dec(v___y_3728_);
    lean_dec_ref(v___y_3727_);
    lean_dec(v___y_3726_);
    lean_dec_ref(v___y_3725_);
    lean_dec(v___y_3724_);
    lean_dec_ref(v___y_3723_);
    lean_dec(v___y_3722_);
    lean_dec(v___y_3721_);
    return v_res_3732_;
}
pub unsafe fn l_Lean_Meta_Grind_proveHEq_x3f(
    mut v_lhs_3733_: *mut LeanObject,
    mut v_rhs_3734_: *mut LeanObject,
    mut v_a_3735_: *mut LeanObject,
    mut v_a_3736_: *mut LeanObject,
    mut v_a_3737_: *mut LeanObject,
    mut v_a_3738_: *mut LeanObject,
    mut v_a_3739_: *mut LeanObject,
    mut v_a_3740_: *mut LeanObject,
    mut v_a_3741_: *mut LeanObject,
    mut v_a_3742_: *mut LeanObject,
    mut v_a_3743_: *mut LeanObject,
    mut v_a_3744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut v_a_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3775_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_isSharedCheck_3780_: u8 = 0;
    let mut v_a_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3784_: u8 = 0;
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3788_: u8 = 0;
    let mut v_a_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: u8 = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_rhs_3734_);
                lean_inc_ref(v_lhs_3733_);
                v___f_3746_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_proveHEq_x3f___lam__0___boxed as *mut core::ffi::c_void,
                    13,
                    2,
                );
                lean_closure_set(v___f_3746_, 0, v_lhs_3733_);
                lean_closure_set(v___f_3746_, 1, v_rhs_3734_);
                v___x_3797_ =
                    l_Lean_Meta_Grind_alreadyInternalized___redArg(v_lhs_3733_, v_a_3735_);
                if lean_obj_tag(v___x_3797_) == 0 {
                    v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
                    lean_inc(v_a_3798_);
                    v___x_3799_ = (lean_unbox(v_a_3798_) as u8);
                    lean_dec(v_a_3798_);
                    if v___x_3799_ == 0 {
                        v___y_3748_ = v___x_3797_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_3797_, 1);
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
                if lean_obj_tag(v___y_3748_) == 0 {
                    v_a_3749_ = lean_ctor_get(v___y_3748_, 0);
                    lean_inc(v_a_3749_);
                    lean_dec_ref_known(v___y_3748_, 1);
                    v___x_3750_ = (lean_unbox(v_a_3749_) as u8);
                    lean_dec(v_a_3749_);
                    if v___x_3750_ == 0 {
                        lean_dec_ref(v_rhs_3734_);
                        lean_dec_ref(v_lhs_3733_);
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
                        lean_dec_ref(v___f_3746_);
                        v___x_3752_ =
                            l_Lean_Meta_Grind_isEqv___redArg(v_lhs_3733_, v_rhs_3734_, v_a_3735_);
                        if lean_obj_tag(v___x_3752_) == 0 {
                            v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
                            v_isSharedCheck_3780_ = (!lean_is_exclusive(v___x_3752_)) as u8;
                            if v_isSharedCheck_3780_ == 0 {
                                v___x_3755_ = v___x_3752_;
                                v_isShared_3756_ = v_isSharedCheck_3780_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3753_);
                                lean_dec(v___x_3752_);
                                v___x_3755_ = lean_box(0);
                                v_isShared_3756_ = v_isSharedCheck_3780_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_rhs_3734_);
                            lean_dec_ref(v_lhs_3733_);
                            v_a_3781_ = lean_ctor_get(v___x_3752_, 0);
                            v_isSharedCheck_3788_ = (!lean_is_exclusive(v___x_3752_)) as u8;
                            if v_isSharedCheck_3788_ == 0 {
                                v___x_3783_ = v___x_3752_;
                                v_isShared_3784_ = v_isSharedCheck_3788_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3781_);
                                lean_dec(v___x_3752_);
                                v___x_3783_ = lean_box(0);
                                v_isShared_3784_ = v_isSharedCheck_3788_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___f_3746_);
                    lean_dec_ref(v_rhs_3734_);
                    lean_dec_ref(v_lhs_3733_);
                    v_a_3789_ = lean_ctor_get(v___y_3748_, 0);
                    v_isSharedCheck_3796_ = (!lean_is_exclusive(v___y_3748_)) as u8;
                    if v_isSharedCheck_3796_ == 0 {
                        v___x_3791_ = v___y_3748_;
                        v_isShared_3792_ = v_isSharedCheck_3796_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3789_);
                        lean_dec(v___y_3748_);
                        v___x_3791_ = lean_box(0);
                        v_isShared_3792_ = v_isSharedCheck_3796_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3757_ = (lean_unbox(v_a_3753_) as u8);
                lean_dec(v_a_3753_);
                if v___x_3757_ == 0 {
                    lean_dec_ref(v_rhs_3734_);
                    lean_dec_ref(v_lhs_3733_);
                    v___x_3758_ = lean_box(0);
                    if v_isShared_3756_ == 0 {
                        lean_ctor_set(v___x_3755_, 0, v___x_3758_);
                        v___x_3760_ = v___x_3755_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
                        v___x_3760_ = v_reuseFailAlloc_3761_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3755_);
                    lean_inc(v_a_3744_);
                    lean_inc_ref(v_a_3743_);
                    lean_inc(v_a_3742_);
                    lean_inc_ref(v_a_3741_);
                    lean_inc(v_a_3740_);
                    lean_inc_ref(v_a_3739_);
                    lean_inc(v_a_3738_);
                    lean_inc_ref(v_a_3737_);
                    lean_inc(v_a_3736_);
                    lean_inc(v_a_3735_);
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
                    if lean_obj_tag(v___x_3762_) == 0 {
                        v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
                        v_isSharedCheck_3771_ = (!lean_is_exclusive(v___x_3762_)) as u8;
                        if v_isSharedCheck_3771_ == 0 {
                            v___x_3765_ = v___x_3762_;
                            v_isShared_3766_ = v_isSharedCheck_3771_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3763_);
                            lean_dec(v___x_3762_);
                            v___x_3765_ = lean_box(0);
                            v_isShared_3766_ = v_isSharedCheck_3771_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3772_ = lean_ctor_get(v___x_3762_, 0);
                        v_isSharedCheck_3779_ = (!lean_is_exclusive(v___x_3762_)) as u8;
                        if v_isSharedCheck_3779_ == 0 {
                            v___x_3774_ = v___x_3762_;
                            v_isShared_3775_ = v_isSharedCheck_3779_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3772_);
                            lean_dec(v___x_3762_);
                            v___x_3774_ = lean_box(0);
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
                v___x_3767_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3767_, 0, v_a_3763_);
                if v_isShared_3766_ == 0 {
                    lean_ctor_set(v___x_3765_, 0, v___x_3767_);
                    v___x_3769_ = v___x_3765_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
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
                    v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
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
                    v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
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
                    v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
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
    mut v_lhs_3801_: *mut LeanObject,
    mut v_rhs_3802_: *mut LeanObject,
    mut v_a_3803_: *mut LeanObject,
    mut v_a_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
    mut v_a_3807_: *mut LeanObject,
    mut v_a_3808_: *mut LeanObject,
    mut v_a_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
    mut v_a_3811_: *mut LeanObject,
    mut v_a_3812_: *mut LeanObject,
    mut v_a_3813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3814_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3812_);
    lean_dec_ref(v_a_3811_);
    lean_dec(v_a_3810_);
    lean_dec_ref(v_a_3809_);
    lean_dec(v_a_3808_);
    lean_dec_ref(v_a_3807_);
    lean_dec(v_a_3806_);
    lean_dec_ref(v_a_3805_);
    lean_dec(v_a_3804_);
    lean_dec(v_a_3803_);
    return v_res_3814_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
}
