// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Main
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.Simp.Simproc Lean.Meta.Sym.Simp.App Lean.Meta.Sym.Simp.Have Lean.Meta.Sym.Simp.Forall
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_mdata___override;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
};
use crate::r#gen::Lean::Meta::Sym::Simp::App::{
    initialize_Lean_Meta_Sym_Simp_App, l_Lean_Meta_Sym_Simp_simpAppArgs,
    runtime_initialize_Lean_Meta_Sym_Simp_App,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Forall::{
    initialize_Lean_Meta_Sym_Simp_Forall, l_Lean_Meta_Sym_Simp_simpForall,
    runtime_initialize_Lean_Meta_Sym_Simp_Forall,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Have::{
    initialize_Lean_Meta_Sym_Simp_Have, l_Lean_Meta_Sym_Simp_simpLet,
    runtime_initialize_Lean_Meta_Sym_Simp_Have,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Lambda::l_Lean_Meta_Sym_Simp_simpLambda;
use crate::r#gen::Lean::Meta::Sym::Simp::Result::l_Lean_Meta_Sym_Simp_mkEqTrans___redArg;
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_Result_withContextDependent,
    l_Lean_Meta_Sym_Simp_getConfig___redArg, l_Lean_Meta_Sym_Simp_mkRflResultCD,
    runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Simproc::{
    initialize_Lean_Meta_Sym_Simp_Simproc, runtime_initialize_Lean_Meta_Sym_Simp_Simproc,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Sym::Simp::SimpM::lean_sym_simp;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_11, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 99, 104, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,16563840882919605222 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,1645835878810041074 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,8664779325712647509 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,14221372908912151252 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__8_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__10_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,4607919608188261591 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__12_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,11919047069369637415 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 97, 105, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__14_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,10074256174017916366 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__16_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5408044218479254519 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__17_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,17572093040211455114 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__18_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,13921602522501100334 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__19_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,1621554907026940391 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__20_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,1768631499306749207 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__21_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__22_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,11365235425757742694 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__23_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__24_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,16365837944853263767 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__25_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,17337110989291206314 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__26_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__9_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,10622541848992288398 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__27_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__11_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,9214941792937935623 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__28_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__13_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,942279487985693879 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__29_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__15_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject,7317983228777666814 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value:
    LeanStringObject<56> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 56,
    m_capacity: 56,
    m_length: 55,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 101, 114, 110, 101, 108, 32, 112,
        114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 101, 114, 109, 32, 100, 117, 114, 105,
        110, 103, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_value:
    LeanStringObject<54> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        10, 112, 114, 101, 45, 112, 114, 111, 99, 101, 115, 115, 32, 97, 110, 100, 32, 102, 111,
        108, 100, 32, 116, 104, 101, 109, 32, 97, 115, 32, 112, 114, 111, 106, 101, 99, 116, 105,
        111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut LeanObject],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_value:
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
            l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0_value
        ) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        112, 101, 114, 115, 105, 115, 116, 101, 110, 116, 32, 99, 97, 99, 104, 101, 32, 104, 105,
        116, 58, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5_value:
    LeanStringObject<22> = LeanStringObject {
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
        116, 114, 97, 110, 115, 105, 101, 110, 116, 32, 99, 97, 99, 104, 101, 32, 104, 105, 116,
        58, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7_value:
    LeanStringObject<48> = LeanStringObject {
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
        96, 115, 105, 109, 112, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 109, 97, 120, 105,
        109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 115, 116, 101, 112, 115,
        32, 101, 120, 99, 101, 101, 100, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___x_1565_ = lean_unsigned_to_nat(2936340881);
    v___x_1566_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__30_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
    v___x_1567_ = l_Lean_Name_num___override(v___x_1566_, v___x_1565_);
    return v___x_1567_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1569_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__32_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
    v___x_1570_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__31_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
    v___x_1571_ = l_Lean_Name_str___override(v___x_1570_, v___x_1569_);
    return v___x_1571_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__34_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
    v___x_1574_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__33_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
    v___x_1575_ = l_Lean_Name_str___override(v___x_1574_, v___x_1573_);
    return v___x_1575_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_unsigned_to_nat(2);
    v___x_1577_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__35_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
    v___x_1578_ = l_Lean_Name_num___override(v___x_1577_, v___x_1576_);
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
    v___x_1581_ = 0;
    v___x_1582_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__36_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_);
    v___x_1583_ = l_Lean_registerTraceClass(v___x_1580_, v___x_1581_, v___x_1582_);
    return v___x_1583_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2____boxed(
    mut v_a_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1585_: *mut LeanObject = core::ptr::null_mut();
    v_res_1585_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
    return v_res_1585_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(
    mut v_d_1586_: *mut LeanObject,
    mut v_e_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
    mut v___y_1591_: *mut LeanObject,
    mut v___y_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1600_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1599_ = lean_st_ref_get(v___y_1589_);
                v_debug_1600_ = lean_ctor_get_uint8(
                    v___x_1599_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_1599_);
                if v_debug_1600_ == 0 {
                    v___y_1596_ = v___y_1589_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_e_1587_);
                    v___x_1601_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_e_1587_,
                        v___y_1588_,
                        v___y_1589_,
                        v___y_1590_,
                        v___y_1591_,
                        v___y_1592_,
                        v___y_1593_,
                    );
                    if lean_obj_tag(v___x_1601_) == 0 {
                        lean_dec_ref_known(v___x_1601_, 1);
                        v___y_1596_ = v___y_1589_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_e_1587_);
                        lean_dec(v_d_1586_);
                        v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
                        v_isSharedCheck_1609_ = (!lean_is_exclusive(v___x_1601_)) as u8;
                        if v_isSharedCheck_1609_ == 0 {
                            v___x_1604_ = v___x_1601_;
                            v_isShared_1605_ = v_isSharedCheck_1609_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1602_);
                            lean_dec(v___x_1601_);
                            v___x_1604_ = lean_box(0);
                            v_isShared_1605_ = v_isSharedCheck_1609_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1597_ = l_Lean_Expr_mdata___override(v_d_1586_, v_e_1587_);
                v___x_1598_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1597_, v___y_1596_);
                return v___x_1598_;
            }
            2 => {
                if v_isShared_1605_ == 0 {
                    v___x_1607_ = v___x_1604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
                    v___x_1607_ = v_reuseFailAlloc_1608_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(
    mut v_d_1610_: *mut LeanObject,
    mut v_e_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1619_: *mut LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_1610_, v_e_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
    lean_dec(v___y_1617_);
    lean_dec_ref(v___y_1616_);
    lean_dec(v___y_1615_);
    lean_dec_ref(v___y_1614_);
    lean_dec(v___y_1613_);
    lean_dec_ref(v___y_1612_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(
    mut v_d_1620_: *mut LeanObject,
    mut v_e_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_d_1620_, v_e_1621_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(
    mut v_d_1633_: *mut LeanObject,
    mut v_e_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1645_: *mut LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(v_d_1633_, v_e_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
    lean_dec(v___y_1643_);
    lean_dec_ref(v___y_1642_);
    lean_dec(v___y_1641_);
    lean_dec_ref(v___y_1640_);
    lean_dec(v___y_1639_);
    lean_dec_ref(v___y_1638_);
    lean_dec(v___y_1637_);
    lean_dec_ref(v___y_1636_);
    lean_dec(v___y_1635_);
    return v_res_1645_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(
    mut v_msgData_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v___x_1652_ = lean_st_ref_get(v___y_1650_);
    v_env_1653_ = lean_ctor_get(v___x_1652_, 0);
    lean_inc_ref(v_env_1653_);
    lean_dec(v___x_1652_);
    v___x_1654_ = lean_st_ref_get(v___y_1648_);
    v_mctx_1655_ = lean_ctor_get(v___x_1654_, 0);
    lean_inc_ref(v_mctx_1655_);
    lean_dec(v___x_1654_);
    v_lctx_1656_ = lean_ctor_get(v___y_1647_, 2);
    v_options_1657_ = lean_ctor_get(v___y_1649_, 2);
    lean_inc_ref(v_options_1657_);
    lean_inc_ref(v_lctx_1656_);
    v___x_1658_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1658_, 0, v_env_1653_);
    lean_ctor_set(v___x_1658_, 1, v_mctx_1655_);
    lean_ctor_set(v___x_1658_, 2, v_lctx_1656_);
    lean_ctor_set(v___x_1658_, 3, v_options_1657_);
    v___x_1659_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1659_, 0, v___x_1658_);
    lean_ctor_set(v___x_1659_, 1, v_msgData_1646_);
    v___x_1660_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1660_, 0, v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(
    mut v_msgData_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1667_: *mut LeanObject = core::ptr::null_mut();
    v_res_1667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msgData_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
    lean_dec(v___y_1665_);
    lean_dec_ref(v___y_1664_);
    lean_dec(v___y_1663_);
    lean_dec_ref(v___y_1662_);
    return v_res_1667_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(
    mut v_msg_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1674_ = lean_ctor_get(v___y_1671_, 5);
                v___x_1675_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
                v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
                v_isSharedCheck_1684_ = (!lean_is_exclusive(v___x_1675_)) as u8;
                if v_isSharedCheck_1684_ == 0 {
                    v___x_1678_ = v___x_1675_;
                    v_isShared_1679_ = v_isSharedCheck_1684_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1676_);
                    lean_dec(v___x_1675_);
                    v___x_1678_ = lean_box(0);
                    v_isShared_1679_ = v_isSharedCheck_1684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1674_);
                v___x_1680_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1680_, 0, v_ref_1674_);
                lean_ctor_set(v___x_1680_, 1, v_a_1676_);
                if v_isShared_1679_ == 0 {
                    lean_ctor_set_tag(v___x_1678_, 1);
                    lean_ctor_set(v___x_1678_, 0, v___x_1680_);
                    v___x_1682_ = v___x_1678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
                    v___x_1682_ = v_reuseFailAlloc_1683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(
    mut v_msg_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1691_: *mut LeanObject = core::ptr::null_mut();
    v_res_1691_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
    lean_dec(v___y_1689_);
    lean_dec_ref(v___y_1688_);
    lean_dec(v___y_1687_);
    lean_dec_ref(v___y_1686_);
    return v_res_1691_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1()
-> *mut LeanObject {
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    v___x_1693_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0;
    v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
    return v___x_1694_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3()
-> *mut LeanObject {
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    v___x_1696_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2;
    v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(
    mut v_e_1700_: *mut LeanObject,
    mut v_a_1701_: *mut LeanObject,
    mut v_a_1702_: *mut LeanObject,
    mut v_a_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
    mut v_a_1706_: *mut LeanObject,
    mut v_a_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_a_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v_contextDependent_1722_: u8 = 0;
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1729_: u8 = 0;
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut v_a_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1749_: u8 = 0;
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_1700_) {
                5 => {
                    v___x_1711_ = l_Lean_Meta_Sym_Simp_simpAppArgs(
                        v_e_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_,
                        v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    );
                    return v___x_1711_;
                }
                6 => {
                    v___x_1712_ = l_Lean_Meta_Sym_Simp_simpLambda(
                        v_e_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_,
                        v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    );
                    return v___x_1712_;
                }
                7 => {
                    v___x_1713_ = l_Lean_Meta_Sym_Simp_simpForall(
                        v_e_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_,
                        v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    );
                    return v___x_1713_;
                }
                8 => {
                    v___x_1714_ = l_Lean_Meta_Sym_Simp_simpLet(
                        v_e_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_,
                        v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
                    );
                    return v___x_1714_;
                }
                10 => {
                    v_data_1715_ = lean_ctor_get(v_e_1700_, 0);
                    lean_inc(v_data_1715_);
                    v_expr_1716_ = lean_ctor_get(v_e_1700_, 1);
                    lean_inc_ref(v_expr_1716_);
                    lean_dec_ref_known(v_e_1700_, 2);
                    lean_inc(v_a_1709_);
                    lean_inc_ref(v_a_1708_);
                    lean_inc(v_a_1707_);
                    lean_inc_ref(v_a_1706_);
                    lean_inc(v_a_1705_);
                    lean_inc_ref(v_a_1704_);
                    lean_inc(v_a_1703_);
                    lean_inc_ref(v_a_1702_);
                    lean_inc(v_a_1701_);
                    v___x_1717_ = lean_sym_simp(
                        v_expr_1716_,
                        v_a_1701_,
                        v_a_1702_,
                        v_a_1703_,
                        v_a_1704_,
                        v_a_1705_,
                        v_a_1706_,
                        v_a_1707_,
                        v_a_1708_,
                        v_a_1709_,
                    );
                    if lean_obj_tag(v___x_1717_) == 0 {
                        v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
                        v_isSharedCheck_1755_ = (!lean_is_exclusive(v___x_1717_)) as u8;
                        if v_isSharedCheck_1755_ == 0 {
                            v___x_1720_ = v___x_1717_;
                            v_isShared_1721_ = v_isSharedCheck_1755_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1718_);
                            lean_dec(v___x_1717_);
                            v___x_1720_ = lean_box(0);
                            v_isShared_1721_ = v_isSharedCheck_1755_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_data_1715_);
                        return v___x_1717_;
                    }
                }
                11 => {
                    v___x_1756_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1);
                    v___x_1757_ = l_Lean_indentExpr(v_e_1700_);
                    v___x_1758_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1758_, 0, v___x_1756_);
                    lean_ctor_set(v___x_1758_, 1, v___x_1757_);
                    v___x_1759_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3);
                    v___x_1760_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1760_, 0, v___x_1758_);
                    lean_ctor_set(v___x_1760_, 1, v___x_1759_);
                    v___x_1761_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_1760_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
                    return v___x_1761_;
                }
                _ => {
                    lean_dec_ref(v_e_1700_);
                    v___x_1762_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4;
                    v___x_1763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    return v___x_1763_;
                }
            },
            1 => {
                if lean_obj_tag(v_a_1718_) == 0 {
                    lean_dec(v_data_1715_);
                    v_contextDependent_1722_ = lean_ctor_get_uint8(v_a_1718_, 1 as u32);
                    lean_dec_ref_known(v_a_1718_, 0);
                    v___x_1723_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_1722_);
                    if v_isShared_1721_ == 0 {
                        lean_ctor_set(v___x_1720_, 0, v___x_1723_);
                        v___x_1725_ = v___x_1720_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
                        v___x_1725_ = v_reuseFailAlloc_1726_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1720_);
                    v_e_x27_1727_ = lean_ctor_get(v_a_1718_, 0);
                    v_proof_1728_ = lean_ctor_get(v_a_1718_, 1);
                    v_contextDependent_1729_ = lean_ctor_get_uint8(
                        v_a_1718_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_1754_ = (!lean_is_exclusive(v_a_1718_)) as u8;
                    if v_isSharedCheck_1754_ == 0 {
                        v___x_1731_ = v_a_1718_;
                        v_isShared_1732_ = v_isSharedCheck_1754_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_proof_1728_);
                        lean_inc(v_e_x27_1727_);
                        lean_dec(v_a_1718_);
                        v___x_1731_ = lean_box(0);
                        v_isShared_1732_ = v_isSharedCheck_1754_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1725_;
            }
            3 => {
                v___x_1733_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(v_data_1715_, v_e_x27_1727_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
                if lean_obj_tag(v___x_1733_) == 0 {
                    v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1745_ = (!lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1736_ = v___x_1733_;
                        v_isShared_1737_ = v_isSharedCheck_1745_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1734_);
                        lean_dec(v___x_1733_);
                        v___x_1736_ = lean_box(0);
                        v_isShared_1737_ = v_isSharedCheck_1745_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1731_);
                    lean_dec_ref(v_proof_1728_);
                    v_a_1746_ = lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1753_ = (!lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1753_ == 0 {
                        v___x_1748_ = v___x_1733_;
                        v_isShared_1749_ = v_isSharedCheck_1753_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1746_);
                        lean_dec(v___x_1733_);
                        v___x_1748_ = lean_box(0);
                        v_isShared_1749_ = v_isSharedCheck_1753_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1738_ = 0;
                if v_isShared_1732_ == 0 {
                    lean_ctor_set(v___x_1731_, 0, v_a_1734_);
                    v___x_1740_ = v___x_1731_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1734_);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_proof_1728_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1744_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_1729_,
                    );
                    v___x_1740_ = v_reuseFailAlloc_1744_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_1740_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1738_,
                );
                if v_isShared_1737_ == 0 {
                    lean_ctor_set(v___x_1736_, 0, v___x_1740_);
                    v___x_1742_ = v___x_1736_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
                    v___x_1742_ = v_reuseFailAlloc_1743_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1742_;
            }
            7 => {
                if v_isShared_1749_ == 0 {
                    v___x_1751_ = v___x_1748_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
                    v___x_1751_ = v_reuseFailAlloc_1752_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(
    mut v_e_1764_: *mut LeanObject,
    mut v_a_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
    mut v_a_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1775_: *mut LeanObject = core::ptr::null_mut();
    v_res_1775_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(
        v_e_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_,
        v_a_1772_, v_a_1773_,
    );
    lean_dec(v_a_1773_);
    lean_dec_ref(v_a_1772_);
    lean_dec(v_a_1771_);
    lean_dec_ref(v_a_1770_);
    lean_dec(v_a_1769_);
    lean_dec_ref(v_a_1768_);
    lean_dec(v_a_1767_);
    lean_dec_ref(v_a_1766_);
    lean_dec(v_a_1765_);
    return v_res_1775_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(
    mut v_00_u03b1_1776_: *mut LeanObject,
    mut v_msg_1777_: *mut LeanObject,
    mut v___y_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v___x_1788_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v_msg_1777_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
    return v___x_1788_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(
    mut v_00_u03b1_1789_: *mut LeanObject,
    mut v_msg_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1801_: *mut LeanObject = core::ptr::null_mut();
    v_res_1801_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(v_00_u03b1_1789_, v_msg_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
    lean_dec(v___y_1799_);
    lean_dec_ref(v___y_1798_);
    lean_dec(v___y_1797_);
    lean_dec_ref(v___y_1796_);
    lean_dec(v___y_1795_);
    lean_dec_ref(v___y_1794_);
    lean_dec(v___y_1793_);
    lean_dec_ref(v___y_1792_);
    lean_dec(v___y_1791_);
    return v_res_1801_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(
    mut v_e_1804_: *mut LeanObject,
    mut v_r_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___f_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___f_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_contextDependent_1844_: u8 = 0;
    let mut v_contextDependent_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_r_1805_) == 0 {
                    v_contextDependent_1844_ = lean_ctor_get_uint8(v_r_1805_, 1 as u32);
                    v___y_1809_ = v_contextDependent_1844_;
                    state = 1;
                    continue;
                } else {
                    v_contextDependent_1845_ = lean_ctor_get_uint8(
                        v_r_1805_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v___y_1809_ = v_contextDependent_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1809_ == 0 {
                    v___x_1810_ = lean_st_ref_take(v_a_1806_);
                    v_numSteps_1811_ = lean_ctor_get(v___x_1810_, 0);
                    v_persistentCache_1812_ = lean_ctor_get(v___x_1810_, 1);
                    v_transientCache_1813_ = lean_ctor_get(v___x_1810_, 2);
                    v_funext_1814_ = lean_ctor_get(v___x_1810_, 3);
                    v_isSharedCheck_1826_ = (!lean_is_exclusive(v___x_1810_)) as u8;
                    if v_isSharedCheck_1826_ == 0 {
                        v___x_1816_ = v___x_1810_;
                        v_isShared_1817_ = v_isSharedCheck_1826_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_funext_1814_);
                        lean_inc(v_transientCache_1813_);
                        lean_inc(v_persistentCache_1812_);
                        lean_inc(v_numSteps_1811_);
                        lean_dec(v___x_1810_);
                        v___x_1816_ = lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1826_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1827_ = lean_st_ref_take(v_a_1806_);
                    v_numSteps_1828_ = lean_ctor_get(v___x_1827_, 0);
                    v_persistentCache_1829_ = lean_ctor_get(v___x_1827_, 1);
                    v_transientCache_1830_ = lean_ctor_get(v___x_1827_, 2);
                    v_funext_1831_ = lean_ctor_get(v___x_1827_, 3);
                    v_isSharedCheck_1843_ = (!lean_is_exclusive(v___x_1827_)) as u8;
                    if v_isSharedCheck_1843_ == 0 {
                        v___x_1833_ = v___x_1827_;
                        v_isShared_1834_ = v_isSharedCheck_1843_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_funext_1831_);
                        lean_inc(v_transientCache_1830_);
                        lean_inc(v_persistentCache_1829_);
                        lean_inc(v_numSteps_1828_);
                        lean_dec(v___x_1827_);
                        v___x_1833_ = lean_box(0);
                        v_isShared_1834_ = v_isSharedCheck_1843_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___f_1818_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
                v___f_1819_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
                lean_inc_ref(v_r_1805_);
                v___x_1820_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1818_,
                    v___f_1819_,
                    v_persistentCache_1812_,
                    v_e_1804_,
                    v_r_1805_,
                );
                if v_isShared_1817_ == 0 {
                    lean_ctor_set(v___x_1816_, 1, v___x_1820_);
                    v___x_1822_ = v___x_1816_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_numSteps_1811_);
                    lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1820_);
                    lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_transientCache_1813_);
                    lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_funext_1814_);
                    v___x_1822_ = v_reuseFailAlloc_1825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1823_ = lean_st_ref_set(v_a_1806_, v___x_1822_);
                v___x_1824_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1824_, 0, v_r_1805_);
                return v___x_1824_;
            }
            4 => {
                v___f_1835_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
                v___f_1836_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
                lean_inc_ref(v_r_1805_);
                v___x_1837_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1835_,
                    v___f_1836_,
                    v_transientCache_1830_,
                    v_e_1804_,
                    v_r_1805_,
                );
                if v_isShared_1834_ == 0 {
                    lean_ctor_set(v___x_1833_, 2, v___x_1837_);
                    v___x_1839_ = v___x_1833_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_numSteps_1828_);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_persistentCache_1829_);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 2, v___x_1837_);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_funext_1831_);
                    v___x_1839_ = v_reuseFailAlloc_1842_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1840_ = lean_st_ref_set(v_a_1806_, v___x_1839_);
                v___x_1841_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1841_, 0, v_r_1805_);
                return v___x_1841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(
    mut v_e_1846_: *mut LeanObject,
    mut v_r_1847_: *mut LeanObject,
    mut v_a_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1850_: *mut LeanObject = core::ptr::null_mut();
    v_res_1850_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(
        v_e_1846_, v_r_1847_, v_a_1848_,
    );
    lean_dec(v_a_1848_);
    return v_res_1850_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(
    mut v_e_1851_: *mut LeanObject,
    mut v_r_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
    mut v_a_1860_: *mut LeanObject,
    mut v_a_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1864_: u8 = 0;
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___f_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___f_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut v_contextDependent_1899_: u8 = 0;
    let mut v_contextDependent_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_r_1852_) == 0 {
                    v_contextDependent_1899_ = lean_ctor_get_uint8(v_r_1852_, 1 as u32);
                    v___y_1864_ = v_contextDependent_1899_;
                    state = 1;
                    continue;
                } else {
                    v_contextDependent_1900_ = lean_ctor_get_uint8(
                        v_r_1852_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v___y_1864_ = v_contextDependent_1900_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1864_ == 0 {
                    v___x_1865_ = lean_st_ref_take(v_a_1855_);
                    v_numSteps_1866_ = lean_ctor_get(v___x_1865_, 0);
                    v_persistentCache_1867_ = lean_ctor_get(v___x_1865_, 1);
                    v_transientCache_1868_ = lean_ctor_get(v___x_1865_, 2);
                    v_funext_1869_ = lean_ctor_get(v___x_1865_, 3);
                    v_isSharedCheck_1881_ = (!lean_is_exclusive(v___x_1865_)) as u8;
                    if v_isSharedCheck_1881_ == 0 {
                        v___x_1871_ = v___x_1865_;
                        v_isShared_1872_ = v_isSharedCheck_1881_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_funext_1869_);
                        lean_inc(v_transientCache_1868_);
                        lean_inc(v_persistentCache_1867_);
                        lean_inc(v_numSteps_1866_);
                        lean_dec(v___x_1865_);
                        v___x_1871_ = lean_box(0);
                        v_isShared_1872_ = v_isSharedCheck_1881_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1882_ = lean_st_ref_take(v_a_1855_);
                    v_numSteps_1883_ = lean_ctor_get(v___x_1882_, 0);
                    v_persistentCache_1884_ = lean_ctor_get(v___x_1882_, 1);
                    v_transientCache_1885_ = lean_ctor_get(v___x_1882_, 2);
                    v_funext_1886_ = lean_ctor_get(v___x_1882_, 3);
                    v_isSharedCheck_1898_ = (!lean_is_exclusive(v___x_1882_)) as u8;
                    if v_isSharedCheck_1898_ == 0 {
                        v___x_1888_ = v___x_1882_;
                        v_isShared_1889_ = v_isSharedCheck_1898_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_funext_1886_);
                        lean_inc(v_transientCache_1885_);
                        lean_inc(v_persistentCache_1884_);
                        lean_inc(v_numSteps_1883_);
                        lean_dec(v___x_1882_);
                        v___x_1888_ = lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1898_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___f_1873_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
                v___f_1874_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
                lean_inc_ref(v_r_1852_);
                v___x_1875_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1873_,
                    v___f_1874_,
                    v_persistentCache_1867_,
                    v_e_1851_,
                    v_r_1852_,
                );
                if v_isShared_1872_ == 0 {
                    lean_ctor_set(v___x_1871_, 1, v___x_1875_);
                    v___x_1877_ = v___x_1871_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_numSteps_1866_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1875_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_transientCache_1868_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_funext_1869_);
                    v___x_1877_ = v_reuseFailAlloc_1880_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1878_ = lean_st_ref_set(v_a_1855_, v___x_1877_);
                v___x_1879_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1879_, 0, v_r_1852_);
                return v___x_1879_;
            }
            4 => {
                v___f_1890_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
                v___f_1891_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
                lean_inc_ref(v_r_1852_);
                v___x_1892_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1890_,
                    v___f_1891_,
                    v_transientCache_1885_,
                    v_e_1851_,
                    v_r_1852_,
                );
                if v_isShared_1889_ == 0 {
                    lean_ctor_set(v___x_1888_, 2, v___x_1892_);
                    v___x_1894_ = v___x_1888_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_numSteps_1883_);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_persistentCache_1884_);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 2, v___x_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_funext_1886_);
                    v___x_1894_ = v_reuseFailAlloc_1897_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1895_ = lean_st_ref_set(v_a_1855_, v___x_1894_);
                v___x_1896_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1896_, 0, v_r_1852_);
                return v___x_1896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(
    mut v_e_1901_: *mut LeanObject,
    mut v_r_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
    mut v_a_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1913_: *mut LeanObject = core::ptr::null_mut();
    v_res_1913_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(
        v_e_1901_, v_r_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_,
        v_a_1909_, v_a_1910_, v_a_1911_,
    );
    lean_dec(v_a_1911_);
    lean_dec_ref(v_a_1910_);
    lean_dec(v_a_1909_);
    lean_dec_ref(v_a_1908_);
    lean_dec(v_a_1907_);
    lean_dec_ref(v_a_1906_);
    lean_dec(v_a_1905_);
    lean_dec_ref(v_a_1904_);
    lean_dec(v_a_1903_);
    return v_res_1913_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1920_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1920_, 0, v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    v___x_1921_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__3);
    v___x_1922_ = l_Lean_MessageData_ofFormat(v___x_1921_);
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1923_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__4);
    v___x_1924_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__2;
    v___x_1925_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    lean_ctor_set(v___x_1925_, 1, v___x_1923_);
    return v___x_1925_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(
    mut v_ref_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    v___x_1928_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___closed__5);
    v___x_1929_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1929_, 0, v_ref_1926_);
    lean_ctor_set(v___x_1929_, 1, v___x_1928_);
    v___x_1930_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1930_, 0, v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg___boxed(
    mut v_ref_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1931_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(
    mut v_00_u03b1_1934_: *mut LeanObject,
    mut v_ref_1935_: *mut LeanObject,
    mut v___y_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    v___x_1946_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_1935_);
    return v___x_1946_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___boxed(
    mut v_00_u03b1_1947_: *mut LeanObject,
    mut v_ref_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1959_: *mut LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3(v_00_u03b1_1947_, v_ref_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
    lean_dec(v___y_1957_);
    lean_dec_ref(v___y_1956_);
    lean_dec(v___y_1955_);
    lean_dec_ref(v___y_1954_);
    lean_dec(v___y_1953_);
    lean_dec_ref(v___y_1952_);
    lean_dec(v___y_1951_);
    lean_dec_ref(v___y_1950_);
    lean_dec(v___y_1949_);
    return v_res_1959_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(
    mut v_x_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
    mut v___y_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_post_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v_post_1972_ = lean_ctor_get(v___y_1962_, 1);
    lean_inc_ref(v_post_1972_);
    lean_inc(v___y_1970_);
    lean_inc_ref(v___y_1969_);
    lean_inc(v___y_1968_);
    lean_inc_ref(v___y_1967_);
    lean_inc(v___y_1966_);
    lean_inc_ref(v___y_1965_);
    lean_inc(v___y_1964_);
    lean_inc_ref(v___y_1963_);
    lean_inc(v___y_1962_);
    v___x_1973_ = lean_apply_11(
        v_post_1972_,
        v___y_1961_,
        v___y_1962_,
        v___y_1963_,
        v___y_1964_,
        v___y_1965_,
        v___y_1966_,
        v___y_1967_,
        v___y_1968_,
        v___y_1969_,
        v___y_1970_,
        lean_box(0),
    );
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(
    mut v_x_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1986_: *mut LeanObject = core::ptr::null_mut();
    v_res_1986_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(
        v_x_1974_,
        v___y_1975_,
        v___y_1976_,
        v___y_1977_,
        v___y_1978_,
        v___y_1979_,
        v___y_1980_,
        v___y_1981_,
        v___y_1982_,
        v___y_1983_,
        v___y_1984_,
    );
    lean_dec(v___y_1984_);
    lean_dec_ref(v___y_1983_);
    lean_dec(v___y_1982_);
    lean_dec_ref(v___y_1981_);
    lean_dec(v___y_1980_);
    lean_dec_ref(v___y_1979_);
    lean_dec(v___y_1978_);
    lean_dec_ref(v___y_1977_);
    lean_dec(v___y_1976_);
    return v_res_1986_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_x_1987_: *mut LeanObject,
    mut v_x_1988_: *mut LeanObject,
    mut v_x_1989_: *mut LeanObject,
    mut v_x_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1991_ = lean_ctor_get(v_x_1987_, 0);
                v_vs_1992_ = lean_ctor_get(v_x_1987_, 1);
                v_isSharedCheck_2016_ = (!lean_is_exclusive(v_x_1987_)) as u8;
                if v_isSharedCheck_2016_ == 0 {
                    v___x_1994_ = v_x_1987_;
                    v_isShared_1995_ = v_isSharedCheck_2016_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1992_);
                    lean_inc(v_ks_1991_);
                    lean_dec(v_x_1987_);
                    v___x_1994_ = lean_box(0);
                    v_isShared_1995_ = v_isSharedCheck_2016_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1996_ = lean_array_get_size(v_ks_1991_);
                v___x_1997_ = lean_nat_dec_lt(v_x_1988_, v___x_1996_);
                if v___x_1997_ == 0 {
                    lean_dec(v_x_1988_);
                    v___x_1998_ = lean_array_push(v_ks_1991_, v_x_1989_);
                    v___x_1999_ = lean_array_push(v_vs_1992_, v_x_1990_);
                    if v_isShared_1995_ == 0 {
                        lean_ctor_set(v___x_1994_, 1, v___x_1999_);
                        lean_ctor_set(v___x_1994_, 0, v___x_1998_);
                        v___x_2001_ = v___x_1994_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
                        lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
                        v___x_2001_ = v_reuseFailAlloc_2002_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2003_ = lean_array_fget_borrowed(v_ks_1991_, v_x_1988_);
                    v___x_2004_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1989_,
                            v_k_x27_2003_,
                        );
                    if v___x_2004_ == 0 {
                        if v_isShared_1995_ == 0 {
                            v___x_2006_ = v___x_1994_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_ks_1991_);
                            lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_vs_1992_);
                            v___x_2006_ = v_reuseFailAlloc_2010_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2011_ = lean_array_fset(v_ks_1991_, v_x_1988_, v_x_1989_);
                        v___x_2012_ = lean_array_fset(v_vs_1992_, v_x_1988_, v_x_1990_);
                        lean_dec(v_x_1988_);
                        if v_isShared_1995_ == 0 {
                            lean_ctor_set(v___x_1994_, 1, v___x_2012_);
                            lean_ctor_set(v___x_1994_, 0, v___x_2011_);
                            v___x_2014_ = v___x_1994_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2011_);
                            lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___x_2012_);
                            v___x_2014_ = v_reuseFailAlloc_2015_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2001_;
            }
            3 => {
                v___x_2007_ = lean_unsigned_to_nat(1);
                v___x_2008_ = lean_nat_add(v_x_1988_, v___x_2007_);
                lean_dec(v_x_1988_);
                v_x_1987_ = v___x_2006_;
                v_x_1988_ = v___x_2008_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(
    mut v_n_2017_: *mut LeanObject,
    mut v_k_2018_: *mut LeanObject,
    mut v_v_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = lean_unsigned_to_nat(0);
    v___x_2021_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_n_2017_, v___x_2020_, v_k_2018_, v_v_2019_);
    return v___x_2021_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2022_: usize = 0;
    let mut v___x_2023_: usize = 0;
    let mut v___x_2024_: usize = 0;
    v___x_2022_ = 5usize;
    v___x_2023_ = 1usize;
    v___x_2024_ = lean_usize_shift_left(v___x_2023_, v___x_2022_);
    return v___x_2024_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2025_: usize = 0;
    let mut v___x_2026_: usize = 0;
    let mut v___x_2027_: usize = 0;
    v___x_2025_ = 1usize;
    v___x_2026_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0);
    v___x_2027_ = lean_usize_sub(v___x_2026_, v___x_2025_);
    return v___x_2027_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2028_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(
    mut v_x_2029_: *mut LeanObject,
    mut v_x_2030_: usize,
    mut v_x_2031_: usize,
    mut v_x_2032_: *mut LeanObject,
    mut v_x_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: usize = 0;
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: usize = 0;
    let mut v_j_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v_v_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v_node_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2070_: usize = 0;
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2078_: u8 = 0;
    let mut v_unused_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: u8 = 0;
    let mut v_ks_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: usize = 0;
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: u8 = 0;
    let mut v_reuseFailAlloc_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2029_) == 0 {
                    v_es_2034_ = lean_ctor_get(v_x_2029_, 0);
                    v___x_2035_ = 5usize;
                    v___x_2036_ = 1usize;
                    v___x_2037_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
                    v___x_2038_ = lean_usize_land(v_x_2030_, v___x_2037_);
                    v_j_2039_ = lean_usize_to_nat(v___x_2038_);
                    v___x_2040_ = lean_array_get_size(v_es_2034_);
                    v___x_2041_ = lean_nat_dec_lt(v_j_2039_, v___x_2040_);
                    if v___x_2041_ == 0 {
                        lean_dec(v_j_2039_);
                        lean_dec(v_x_2033_);
                        lean_dec_ref(v_x_2032_);
                        return v_x_2029_;
                    } else {
                        lean_inc_ref(v_es_2034_);
                        v_isSharedCheck_2078_ = (!lean_is_exclusive(v_x_2029_)) as u8;
                        if v_isSharedCheck_2078_ == 0 {
                            v_unused_2079_ = lean_ctor_get(v_x_2029_, 0);
                            lean_dec(v_unused_2079_);
                            v___x_2043_ = v_x_2029_;
                            v_isShared_2044_ = v_isSharedCheck_2078_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2029_);
                            v___x_2043_ = lean_box(0);
                            v_isShared_2044_ = v_isSharedCheck_2078_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2080_ = lean_ctor_get(v_x_2029_, 0);
                    v_vs_2081_ = lean_ctor_get(v_x_2029_, 1);
                    v_isSharedCheck_2101_ = (!lean_is_exclusive(v_x_2029_)) as u8;
                    if v_isSharedCheck_2101_ == 0 {
                        v___x_2083_ = v_x_2029_;
                        v_isShared_2084_ = v_isSharedCheck_2101_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2081_);
                        lean_inc(v_ks_2080_);
                        lean_dec(v_x_2029_);
                        v___x_2083_ = lean_box(0);
                        v_isShared_2084_ = v_isSharedCheck_2101_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2045_ = lean_array_fget(v_es_2034_, v_j_2039_);
                v___x_2046_ = lean_box(0);
                v_xs_x27_2047_ = lean_array_fset(v_es_2034_, v_j_2039_, v___x_2046_);
                match lean_obj_tag(v_v_2045_) {
                    0 => {
                        v_key_2054_ = lean_ctor_get(v_v_2045_, 0);
                        v_val_2055_ = lean_ctor_get(v_v_2045_, 1);
                        v_isSharedCheck_2065_ = (!lean_is_exclusive(v_v_2045_)) as u8;
                        if v_isSharedCheck_2065_ == 0 {
                            v___x_2057_ = v_v_2045_;
                            v_isShared_2058_ = v_isSharedCheck_2065_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2055_);
                            lean_inc(v_key_2054_);
                            lean_dec(v_v_2045_);
                            v___x_2057_ = lean_box(0);
                            v_isShared_2058_ = v_isSharedCheck_2065_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2066_ = lean_ctor_get(v_v_2045_, 0);
                        v_isSharedCheck_2076_ = (!lean_is_exclusive(v_v_2045_)) as u8;
                        if v_isSharedCheck_2076_ == 0 {
                            v___x_2068_ = v_v_2045_;
                            v_isShared_2069_ = v_isSharedCheck_2076_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2066_);
                            lean_dec(v_v_2045_);
                            v___x_2068_ = lean_box(0);
                            v_isShared_2069_ = v_isSharedCheck_2076_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2077_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2077_, 0, v_x_2032_);
                        lean_ctor_set(v___x_2077_, 1, v_x_2033_);
                        v___y_2049_ = v___x_2077_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2050_ = lean_array_fset(v_xs_x27_2047_, v_j_2039_, v___y_2049_);
                lean_dec(v_j_2039_);
                if v_isShared_2044_ == 0 {
                    lean_ctor_set(v___x_2043_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2043_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2052_;
            }
            4 => {
                v___x_2059_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_2032_,
                        v_key_2054_,
                    );
                if v___x_2059_ == 0 {
                    lean_del_object(v___x_2057_);
                    v___x_2060_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2054_,
                        v_val_2055_,
                        v_x_2032_,
                        v_x_2033_,
                    );
                    v___x_2061_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                    v___y_2049_ = v___x_2061_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2055_);
                    lean_dec(v_key_2054_);
                    if v_isShared_2058_ == 0 {
                        lean_ctor_set(v___x_2057_, 1, v_x_2033_);
                        lean_ctor_set(v___x_2057_, 0, v_x_2032_);
                        v___x_2063_ = v___x_2057_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_x_2032_);
                        lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_x_2033_);
                        v___x_2063_ = v_reuseFailAlloc_2064_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2049_ = v___x_2063_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2070_ = lean_usize_shift_right(v_x_2030_, v___x_2035_);
                v___x_2071_ = lean_usize_add(v_x_2031_, v___x_2036_);
                v___x_2072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_node_2066_, v___x_2070_, v___x_2071_, v_x_2032_, v_x_2033_);
                if v_isShared_2069_ == 0 {
                    lean_ctor_set(v___x_2068_, 0, v___x_2072_);
                    v___x_2074_ = v___x_2068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
                    v___x_2074_ = v_reuseFailAlloc_2075_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2049_ = v___x_2074_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2084_ == 0 {
                    v___x_2086_ = v___x_2083_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_ks_2080_);
                    lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_vs_2081_);
                    v___x_2086_ = v_reuseFailAlloc_2100_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2087_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v___x_2086_, v_x_2032_, v_x_2033_);
                v___x_2095_ = 7usize;
                v___x_2096_ = lean_usize_dec_le(v___x_2095_, v_x_2031_);
                if v___x_2096_ == 0 {
                    v___x_2097_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2087_);
                    v___x_2098_ = lean_unsigned_to_nat(4);
                    v___x_2099_ = lean_nat_dec_lt(v___x_2097_, v___x_2098_);
                    lean_dec(v___x_2097_);
                    v___y_2089_ = v___x_2099_;
                    state = 10;
                    continue;
                } else {
                    v___y_2089_ = v___x_2096_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2089_ == 0 {
                    v_ks_2090_ = lean_ctor_get(v_newNode_2087_, 0);
                    lean_inc_ref(v_ks_2090_);
                    v_vs_2091_ = lean_ctor_get(v_newNode_2087_, 1);
                    lean_inc_ref(v_vs_2091_);
                    lean_dec_ref(v_newNode_2087_);
                    v___x_2092_ = lean_unsigned_to_nat(0);
                    v___x_2093_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2);
                    v___x_2094_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_x_2031_, v_ks_2090_, v_vs_2091_, v___x_2092_, v___x_2093_);
                    lean_dec_ref(v_vs_2091_);
                    lean_dec_ref(v_ks_2090_);
                    return v___x_2094_;
                } else {
                    return v_newNode_2087_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(
    mut v_depth_2102_: usize,
    mut v_keys_2103_: *mut LeanObject,
    mut v_vals_2104_: *mut LeanObject,
    mut v_i_2105_: *mut LeanObject,
    mut v_entries_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v_k_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u64 = 0;
    let mut v_h_2112_: usize = 0;
    let mut v___x_2113_: usize = 0;
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: usize = 0;
    let mut v___x_2116_: usize = 0;
    let mut v___x_2117_: usize = 0;
    let mut v_h_2118_: usize = 0;
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2107_ = lean_array_get_size(v_keys_2103_);
                v___x_2108_ = lean_nat_dec_lt(v_i_2105_, v___x_2107_);
                if v___x_2108_ == 0 {
                    lean_dec(v_i_2105_);
                    return v_entries_2106_;
                } else {
                    v_k_2109_ = lean_array_fget_borrowed(v_keys_2103_, v_i_2105_);
                    v_v_2110_ = lean_array_fget_borrowed(v_vals_2104_, v_i_2105_);
                    v___x_2111_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2109_);
                    v_h_2112_ = lean_uint64_to_usize(v___x_2111_);
                    v___x_2113_ = 5usize;
                    v___x_2114_ = lean_unsigned_to_nat(1);
                    v___x_2115_ = 1usize;
                    v___x_2116_ = lean_usize_sub(v_depth_2102_, v___x_2115_);
                    v___x_2117_ = lean_usize_mul(v___x_2113_, v___x_2116_);
                    v_h_2118_ = lean_usize_shift_right(v_h_2112_, v___x_2117_);
                    v___x_2119_ = lean_nat_add(v_i_2105_, v___x_2114_);
                    lean_dec(v_i_2105_);
                    lean_inc(v_v_2110_);
                    lean_inc(v_k_2109_);
                    v___x_2120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_entries_2106_, v_h_2118_, v_depth_2102_, v_k_2109_, v_v_2110_);
                    v_i_2105_ = v___x_2119_;
                    v_entries_2106_ = v___x_2120_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_depth_2122_: *mut LeanObject,
    mut v_keys_2123_: *mut LeanObject,
    mut v_vals_2124_: *mut LeanObject,
    mut v_i_2125_: *mut LeanObject,
    mut v_entries_2126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2127_: usize = 0;
    let mut v_res_2128_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2127_ = lean_unbox_usize(v_depth_2122_);
    lean_dec(v_depth_2122_);
    v_res_2128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_2127_, v_keys_2123_, v_vals_2124_, v_i_2125_, v_entries_2126_);
    lean_dec_ref(v_vals_2124_);
    lean_dec_ref(v_keys_2123_);
    return v_res_2128_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(
    mut v_x_2129_: *mut LeanObject,
    mut v_x_2130_: *mut LeanObject,
    mut v_x_2131_: *mut LeanObject,
    mut v_x_2132_: *mut LeanObject,
    mut v_x_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_114346__boxed_2134_: usize = 0;
    let mut v_x_114347__boxed_2135_: usize = 0;
    let mut v_res_2136_: *mut LeanObject = core::ptr::null_mut();
    v_x_114346__boxed_2134_ = lean_unbox_usize(v_x_2130_);
    lean_dec(v_x_2130_);
    v_x_114347__boxed_2135_ = lean_unbox_usize(v_x_2131_);
    lean_dec(v_x_2131_);
    v_res_2136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_2129_, v_x_114346__boxed_2134_, v_x_114347__boxed_2135_, v_x_2132_, v_x_2133_);
    return v_res_2136_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(
    mut v_x_2137_: *mut LeanObject,
    mut v_x_2138_: *mut LeanObject,
    mut v_x_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2140_: u64 = 0;
    let mut v___x_2141_: usize = 0;
    let mut v___x_2142_: usize = 0;
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v___x_2140_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2138_);
    v___x_2141_ = lean_uint64_to_usize(v___x_2140_);
    v___x_2142_ = 1usize;
    v___x_2143_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_2137_, v___x_2141_, v___x_2142_, v_x_2138_, v_x_2139_);
    return v___x_2143_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: f64 = 0.0;
    v___x_2144_ = lean_unsigned_to_nat(0);
    v___x_2145_ = lean_float_of_nat(v___x_2144_);
    return v___x_2145_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(
    mut v_cls_2149_: *mut LeanObject,
    mut v_msg_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v_tid_2175_: u64 = 0;
    let mut v_traces_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: f64 = 0.0;
    let mut v___x_2182_: u8 = 0;
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2156_ = lean_ctor_get(v___y_2153_, 5);
                v___x_2157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
                v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
                v_isSharedCheck_2202_ = (!lean_is_exclusive(v___x_2157_)) as u8;
                if v_isSharedCheck_2202_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    v_isShared_2161_ = v_isSharedCheck_2202_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2158_);
                    lean_dec(v___x_2157_);
                    v___x_2160_ = lean_box(0);
                    v_isShared_2161_ = v_isSharedCheck_2202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2162_ = lean_st_ref_take(v___y_2154_);
                v_traceState_2163_ = lean_ctor_get(v___x_2162_, 4);
                v_env_2164_ = lean_ctor_get(v___x_2162_, 0);
                v_nextMacroScope_2165_ = lean_ctor_get(v___x_2162_, 1);
                v_ngen_2166_ = lean_ctor_get(v___x_2162_, 2);
                v_auxDeclNGen_2167_ = lean_ctor_get(v___x_2162_, 3);
                v_cache_2168_ = lean_ctor_get(v___x_2162_, 5);
                v_messages_2169_ = lean_ctor_get(v___x_2162_, 6);
                v_infoState_2170_ = lean_ctor_get(v___x_2162_, 7);
                v_snapshotTasks_2171_ = lean_ctor_get(v___x_2162_, 8);
                v_isSharedCheck_2201_ = (!lean_is_exclusive(v___x_2162_)) as u8;
                if v_isSharedCheck_2201_ == 0 {
                    v___x_2173_ = v___x_2162_;
                    v_isShared_2174_ = v_isSharedCheck_2201_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2171_);
                    lean_inc(v_infoState_2170_);
                    lean_inc(v_messages_2169_);
                    lean_inc(v_cache_2168_);
                    lean_inc(v_traceState_2163_);
                    lean_inc(v_auxDeclNGen_2167_);
                    lean_inc(v_ngen_2166_);
                    lean_inc(v_nextMacroScope_2165_);
                    lean_inc(v_env_2164_);
                    lean_dec(v___x_2162_);
                    v___x_2173_ = lean_box(0);
                    v_isShared_2174_ = v_isSharedCheck_2201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2175_ = lean_ctor_get_uint64(
                    v_traceState_2163_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2176_ = lean_ctor_get(v_traceState_2163_, 0);
                v_isSharedCheck_2200_ = (!lean_is_exclusive(v_traceState_2163_)) as u8;
                if v_isSharedCheck_2200_ == 0 {
                    v___x_2178_ = v_traceState_2163_;
                    v_isShared_2179_ = v_isSharedCheck_2200_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2176_);
                    lean_dec(v_traceState_2163_);
                    v___x_2178_ = lean_box(0);
                    v_isShared_2179_ = v_isSharedCheck_2200_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2180_ = lean_box(0);
                v___x_2181_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
                v___x_2182_ = 0;
                v___x_2183_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1;
                v___x_2184_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2184_, 0, v_cls_2149_);
                lean_ctor_set(v___x_2184_, 1, v___x_2180_);
                lean_ctor_set(v___x_2184_, 2, v___x_2183_);
                lean_ctor_set_float(
                    v___x_2184_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2181_,
                );
                lean_ctor_set_float(
                    v___x_2184_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2181_,
                );
                lean_ctor_set_uint8(
                    v___x_2184_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2182_,
                );
                v___x_2185_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2;
                v___x_2186_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2186_, 0, v___x_2184_);
                lean_ctor_set(v___x_2186_, 1, v_a_2158_);
                lean_ctor_set(v___x_2186_, 2, v___x_2185_);
                lean_inc(v_ref_2156_);
                v___x_2187_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2187_, 0, v_ref_2156_);
                lean_ctor_set(v___x_2187_, 1, v___x_2186_);
                v___x_2188_ = l_Lean_PersistentArray_push___redArg(v_traces_2176_, v___x_2187_);
                if v_isShared_2179_ == 0 {
                    lean_ctor_set(v___x_2178_, 0, v___x_2188_);
                    v___x_2190_ = v___x_2178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2188_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2199_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2175_,
                    );
                    v___x_2190_ = v_reuseFailAlloc_2199_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2174_ == 0 {
                    lean_ctor_set(v___x_2173_, 4, v___x_2190_);
                    v___x_2192_ = v___x_2173_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_env_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_nextMacroScope_2165_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_ngen_2166_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_auxDeclNGen_2167_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 4, v___x_2190_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_cache_2168_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_messages_2169_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_infoState_2170_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_snapshotTasks_2171_);
                    v___x_2192_ = v_reuseFailAlloc_2198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2193_ = lean_st_ref_set(v___y_2154_, v___x_2192_);
                v___x_2194_ = lean_box(0);
                if v_isShared_2161_ == 0 {
                    lean_ctor_set(v___x_2160_, 0, v___x_2194_);
                    v___x_2196_ = v___x_2160_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(
    mut v_cls_2203_: *mut LeanObject,
    mut v_msg_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_2203_, v_msg_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
    lean_dec(v___y_2208_);
    lean_dec_ref(v___y_2207_);
    lean_dec(v___y_2206_);
    lean_dec_ref(v___y_2205_);
    return v_res_2210_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(
    mut v_keys_2211_: *mut LeanObject,
    mut v_vals_2212_: *mut LeanObject,
    mut v_i_2213_: *mut LeanObject,
    mut v_k_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2215_ = lean_array_get_size(v_keys_2211_);
                v___x_2216_ = lean_nat_dec_lt(v_i_2213_, v___x_2215_);
                if v___x_2216_ == 0 {
                    lean_dec(v_i_2213_);
                    v___x_2217_ = lean_box(0);
                    return v___x_2217_;
                } else {
                    v_k_x27_2218_ = lean_array_fget_borrowed(v_keys_2211_, v_i_2213_);
                    v___x_2219_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2214_,
                            v_k_x27_2218_,
                        );
                    if v___x_2219_ == 0 {
                        v___x_2220_ = lean_unsigned_to_nat(1);
                        v___x_2221_ = lean_nat_add(v_i_2213_, v___x_2220_);
                        lean_dec(v_i_2213_);
                        v_i_2213_ = v___x_2221_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2223_ = lean_array_fget_borrowed(v_vals_2212_, v_i_2213_);
                        lean_dec(v_i_2213_);
                        lean_inc(v___x_2223_);
                        v___x_2224_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2224_, 0, v___x_2223_);
                        return v___x_2224_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_keys_2225_: *mut LeanObject,
    mut v_vals_2226_: *mut LeanObject,
    mut v_i_2227_: *mut LeanObject,
    mut v_k_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2229_: *mut LeanObject = core::ptr::null_mut();
    v_res_2229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_2225_, v_vals_2226_, v_i_2227_, v_k_2228_);
    lean_dec_ref(v_k_2228_);
    lean_dec_ref(v_vals_2226_);
    lean_dec_ref(v_keys_2225_);
    return v_res_2229_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(
    mut v_x_2230_: *mut LeanObject,
    mut v_x_2231_: usize,
    mut v_x_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: usize = 0;
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: usize = 0;
    let mut v_j_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: usize = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2230_) == 0 {
                    v_es_2233_ = lean_ctor_get(v_x_2230_, 0);
                    v___x_2234_ = lean_box(2);
                    v___x_2235_ = 5usize;
                    v___x_2236_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1);
                    v___x_2237_ = lean_usize_land(v_x_2231_, v___x_2236_);
                    v_j_2238_ = lean_usize_to_nat(v___x_2237_);
                    v___x_2239_ = lean_array_get_borrowed(v___x_2234_, v_es_2233_, v_j_2238_);
                    lean_dec(v_j_2238_);
                    match lean_obj_tag(v___x_2239_) {
                        0 => {
                            v_key_2240_ = lean_ctor_get(v___x_2239_, 0);
                            v_val_2241_ = lean_ctor_get(v___x_2239_, 1);
                            v___x_2242_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2232_, v_key_2240_);
                            if v___x_2242_ == 0 {
                                v___x_2243_ = lean_box(0);
                                return v___x_2243_;
                            } else {
                                lean_inc(v_val_2241_);
                                v___x_2244_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2244_, 0, v_val_2241_);
                                return v___x_2244_;
                            }
                        }
                        1 => {
                            v_node_2245_ = lean_ctor_get(v___x_2239_, 0);
                            v___x_2246_ = lean_usize_shift_right(v_x_2231_, v___x_2235_);
                            v_x_2230_ = v_node_2245_;
                            v_x_2231_ = v___x_2246_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2248_ = lean_box(0);
                            return v___x_2248_;
                        }
                    }
                } else {
                    v_ks_2249_ = lean_ctor_get(v_x_2230_, 0);
                    v_vs_2250_ = lean_ctor_get(v_x_2230_, 1);
                    v___x_2251_ = lean_unsigned_to_nat(0);
                    v___x_2252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_ks_2249_, v_vs_2250_, v___x_2251_, v_x_2232_);
                    return v___x_2252_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(
    mut v_x_2253_: *mut LeanObject,
    mut v_x_2254_: *mut LeanObject,
    mut v_x_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_114647__boxed_2256_: usize = 0;
    let mut v_res_2257_: *mut LeanObject = core::ptr::null_mut();
    v_x_114647__boxed_2256_ = lean_unbox_usize(v_x_2254_);
    lean_dec(v_x_2254_);
    v_res_2257_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_2253_, v_x_114647__boxed_2256_, v_x_2255_);
    lean_dec_ref(v_x_2255_);
    lean_dec_ref(v_x_2253_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(
    mut v_x_2258_: *mut LeanObject,
    mut v_x_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: u64 = 0;
    let mut v___x_2261_: usize = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2259_);
    v___x_2261_ = lean_uint64_to_usize(v___x_2260_);
    v___x_2262_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_2258_, v___x_2261_, v_x_2259_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(
    mut v_x_2263_: *mut LeanObject,
    mut v_x_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2265_: *mut LeanObject = core::ptr::null_mut();
    v_res_2265_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_2263_, v_x_2264_);
    lean_dec_ref(v_x_2264_);
    lean_dec_ref(v_x_2263_);
    return v_res_2265_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2()
-> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    v___x_2269_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
    v___x_2270_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1;
    v___x_2271_ = l_Lean_Name_append(v___x_2270_, v___x_2269_);
    return v___x_2271_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4()
-> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    v___x_2273_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__3;
    v___x_2274_ = l_Lean_stringToMessageData(v___x_2273_);
    return v___x_2274_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6()
-> *mut LeanObject {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2276_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__5;
    v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8()
-> *mut LeanObject {
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    v___x_2279_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__7;
    v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn lean_sym_simp(
    mut v_e_u2081_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: u8 = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut v___y_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2329_: u8 = 0;
    let mut v___y_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: u8 = 0;
    let mut v___y_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2338_: u8 = 0;
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_u2082_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_u2081_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cd_u2081_2343_: u8 = 0;
    let mut v___y_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2355_: u8 = 0;
    let mut v_contextDependent_2356_: u8 = 0;
    let mut v_done_2357_: u8 = 0;
    let mut v_e_x27_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2360_: u8 = 0;
    let mut v_contextDependent_2361_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2368_: u8 = 0;
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut v___y_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2384_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_done_2415_: u8 = 0;
    let mut v_e_x27_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2418_: u8 = 0;
    let mut v_contextDependent_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v___y_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: u8 = 0;
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: u8 = 0;
    let mut v___y_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: u8 = 0;
    let mut v___y_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: u8 = 0;
    let mut v___y_2478_: u8 = 0;
    let mut v___y_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2486_: u8 = 0;
    let mut v___y_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2490_: u8 = 0;
    let mut v_contextDependent_2491_: u8 = 0;
    let mut v___y_2493_: u8 = 0;
    let mut v___y_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: u8 = 0;
    let mut v___y_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: u8 = 0;
    let mut v___y_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: u8 = 0;
    let mut v___y_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: u8 = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: u8 = 0;
    let mut v___y_2523_: u8 = 0;
    let mut v___y_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: u8 = 0;
    let mut v___y_2536_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: u8 = 0;
    let mut v___y_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: u8 = 0;
    let mut v___y_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: u8 = 0;
    let mut v___y_2553_: u8 = 0;
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2567_: u8 = 0;
    let mut v_cancelTk_x3f_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2569_: u8 = 0;
    let mut v_inheritedTraceOptions_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v___y_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v_done_2601_: u8 = 0;
    let mut v_contextDependent_2602_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2606_: u8 = 0;
    let mut v_contextDependent_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2611_: u8 = 0;
    let mut v_contextDependent_2612_: u8 = 0;
    let mut v_done_2613_: u8 = 0;
    let mut v_e_x27_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2616_: u8 = 0;
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2619_: u8 = 0;
    let mut v_contextDependent_2620_: u8 = 0;
    let mut v_done_2621_: u8 = 0;
    let mut v_e_x27_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_2624_: u8 = 0;
    let mut v_contextDependent_2625_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut v_contextDependent_2637_: u8 = 0;
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2645_: u8 = 0;
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_done_2672_: u8 = 0;
    let mut v_e_x27_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2675_: u8 = 0;
    let mut v_contextDependent_2676_: u8 = 0;
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funext_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_unused_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2731_: u8 = 0;
    let mut v_val_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut v_val_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v_inheritedTraceOptions_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: u8 = 0;
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2757_: u8 = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2761_: u8 = 0;
    let mut v_unused_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2770_: u8 = 0;
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2776_: u8 = 0;
    let mut v_val_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_val_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v_inheritedTraceOptions_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_unused_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2815_: u8 = 0;
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_reuseFailAlloc_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2555_ = lean_ctor_get(v_a_2289_, 0);
                v_fileMap_2556_ = lean_ctor_get(v_a_2289_, 1);
                v_options_2557_ = lean_ctor_get(v_a_2289_, 2);
                v_currRecDepth_2558_ = lean_ctor_get(v_a_2289_, 3);
                v_maxRecDepth_2559_ = lean_ctor_get(v_a_2289_, 4);
                v_ref_2560_ = lean_ctor_get(v_a_2289_, 5);
                v_currNamespace_2561_ = lean_ctor_get(v_a_2289_, 6);
                v_openDecls_2562_ = lean_ctor_get(v_a_2289_, 7);
                v_initHeartbeats_2563_ = lean_ctor_get(v_a_2289_, 8);
                v_maxHeartbeats_2564_ = lean_ctor_get(v_a_2289_, 9);
                v_quotContext_2565_ = lean_ctor_get(v_a_2289_, 10);
                v_currMacroScope_2566_ = lean_ctor_get(v_a_2289_, 11);
                v_diag_2567_ = lean_ctor_get_uint8(
                    v_a_2289_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2568_ = lean_ctor_get(v_a_2289_, 12);
                v_suppressElabErrors_2569_ = lean_ctor_get_uint8(
                    v_a_2289_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2570_ = lean_ctor_get(v_a_2289_, 13);
                v_isSharedCheck_2866_ = (!lean_is_exclusive(v_a_2289_)) as u8;
                if v_isSharedCheck_2866_ == 0 {
                    v___x_2572_ = v_a_2289_;
                    v_isShared_2573_ = v_isSharedCheck_2866_;
                    state = 27;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_2570_);
                    lean_inc(v_cancelTk_x3f_2568_);
                    lean_inc(v_currMacroScope_2566_);
                    lean_inc(v_quotContext_2565_);
                    lean_inc(v_maxHeartbeats_2564_);
                    lean_inc(v_initHeartbeats_2563_);
                    lean_inc(v_openDecls_2562_);
                    lean_inc(v_currNamespace_2561_);
                    lean_inc(v_ref_2560_);
                    lean_inc(v_maxRecDepth_2559_);
                    lean_inc(v_currRecDepth_2558_);
                    lean_inc(v_options_2557_);
                    lean_inc(v_fileMap_2556_);
                    lean_inc(v_fileName_2555_);
                    lean_dec(v_a_2289_);
                    v___x_2572_ = lean_box(0);
                    v_isShared_2573_ = v_isSharedCheck_2866_;
                    state = 27;
                    continue;
                }
            }
            1 => {
                if v___y_2295_ == 0 {
                    v___x_2296_ = lean_st_ref_take(v___y_2294_);
                    v_numSteps_2297_ = lean_ctor_get(v___x_2296_, 0);
                    v_persistentCache_2298_ = lean_ctor_get(v___x_2296_, 1);
                    v_transientCache_2299_ = lean_ctor_get(v___x_2296_, 2);
                    v_funext_2300_ = lean_ctor_get(v___x_2296_, 3);
                    v_isSharedCheck_2310_ = (!lean_is_exclusive(v___x_2296_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v___x_2302_ = v___x_2296_;
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_funext_2300_);
                        lean_inc(v_transientCache_2299_);
                        lean_inc(v_persistentCache_2298_);
                        lean_inc(v_numSteps_2297_);
                        lean_dec(v___x_2296_);
                        v___x_2302_ = lean_box(0);
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2311_ = lean_st_ref_take(v___y_2294_);
                    v_numSteps_2312_ = lean_ctor_get(v___x_2311_, 0);
                    v_persistentCache_2313_ = lean_ctor_get(v___x_2311_, 1);
                    v_transientCache_2314_ = lean_ctor_get(v___x_2311_, 2);
                    v_funext_2315_ = lean_ctor_get(v___x_2311_, 3);
                    v_isSharedCheck_2325_ = (!lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2325_ == 0 {
                        v___x_2317_ = v___x_2311_;
                        v_isShared_2318_ = v_isSharedCheck_2325_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_funext_2315_);
                        lean_inc(v_transientCache_2314_);
                        lean_inc(v_persistentCache_2313_);
                        lean_inc(v_numSteps_2312_);
                        lean_dec(v___x_2311_);
                        v___x_2317_ = lean_box(0);
                        v_isShared_2318_ = v_isSharedCheck_2325_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc_ref(v___y_2293_);
                v___x_2304_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_2298_, v_e_u2081_2281_, v___y_2293_);
                if v_isShared_2303_ == 0 {
                    lean_ctor_set(v___x_2302_, 1, v___x_2304_);
                    v___x_2306_ = v___x_2302_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_numSteps_2297_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2304_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_transientCache_2299_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_funext_2300_);
                    v___x_2306_ = v_reuseFailAlloc_2309_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2307_ = lean_st_ref_set(v___y_2294_, v___x_2306_);
                lean_dec(v___y_2294_);
                v___x_2308_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2308_, 0, v___y_2293_);
                return v___x_2308_;
            }
            4 => {
                lean_inc_ref(v___y_2293_);
                v___x_2319_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_2314_, v_e_u2081_2281_, v___y_2293_);
                if v_isShared_2318_ == 0 {
                    lean_ctor_set(v___x_2317_, 2, v___x_2319_);
                    v___x_2321_ = v___x_2317_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_numSteps_2312_);
                    lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_persistentCache_2313_);
                    lean_ctor_set(v_reuseFailAlloc_2324_, 2, v___x_2319_);
                    lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_funext_2315_);
                    v___x_2321_ = v_reuseFailAlloc_2324_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2322_ = lean_st_ref_set(v___y_2294_, v___x_2321_);
                lean_dec(v___y_2294_);
                v___x_2323_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2323_, 0, v___y_2293_);
                return v___x_2323_;
            }
            6 => {
                v___x_2332_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_2332_, 0, v___y_2327_);
                lean_ctor_set(v___x_2332_, 1, v___y_2328_);
                lean_ctor_set_uint8(
                    v___x_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_2329_,
                );
                lean_ctor_set_uint8(
                    v___x_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2331_,
                );
                v___y_2293_ = v___x_2332_;
                v___y_2294_ = v___y_2330_;
                v___y_2295_ = v___y_2331_;
                state = 1;
                continue;
            }
            7 => {
                v___x_2339_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_2339_, 0, v___y_2335_);
                lean_ctor_set(v___x_2339_, 1, v___y_2336_);
                lean_ctor_set_uint8(
                    v___x_2339_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_2334_,
                );
                lean_ctor_set_uint8(
                    v___x_2339_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2338_,
                );
                v___y_2293_ = v___x_2339_;
                v___y_2294_ = v___y_2337_;
                v___y_2295_ = v___y_2338_;
                state = 1;
                continue;
            }
            8 => {
                lean_inc(v___y_2352_);
                lean_inc_ref(v___y_2351_);
                lean_inc(v___y_2350_);
                lean_inc_ref(v___y_2349_);
                lean_inc(v___y_2348_);
                lean_inc(v___y_2346_);
                lean_inc_ref(v_e_u2082_2341_);
                v___x_2353_ = lean_sym_simp(
                    v_e_u2082_2341_,
                    v___y_2344_,
                    v___y_2345_,
                    v___y_2346_,
                    v___y_2347_,
                    v___y_2348_,
                    v___y_2349_,
                    v___y_2350_,
                    v___y_2351_,
                    v___y_2352_,
                );
                if lean_obj_tag(v___x_2353_) == 0 {
                    v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
                    lean_inc(v_a_2354_);
                    lean_dec_ref_known(v___x_2353_, 1);
                    if lean_obj_tag(v_a_2354_) == 0 {
                        lean_dec(v___y_2352_);
                        lean_dec_ref(v___y_2351_);
                        lean_dec(v___y_2350_);
                        lean_dec_ref(v___y_2349_);
                        lean_dec(v___y_2348_);
                        if v_cd_u2081_2343_ == 0 {
                            v_done_2355_ = lean_ctor_get_uint8(v_a_2354_, 0 as u32);
                            v_contextDependent_2356_ = lean_ctor_get_uint8(v_a_2354_, 1 as u32);
                            lean_dec_ref_known(v_a_2354_, 0);
                            v___y_2327_ = v_e_u2082_2341_;
                            v___y_2328_ = v_h_u2081_2342_;
                            v___y_2329_ = v_done_2355_;
                            v___y_2330_ = v___y_2346_;
                            v___y_2331_ = v_contextDependent_2356_;
                            state = 6;
                            continue;
                        } else {
                            v_done_2357_ = lean_ctor_get_uint8(v_a_2354_, 0 as u32);
                            lean_dec_ref_known(v_a_2354_, 0);
                            v___y_2327_ = v_e_u2082_2341_;
                            v___y_2328_ = v_h_u2081_2342_;
                            v___y_2329_ = v_done_2357_;
                            v___y_2330_ = v___y_2346_;
                            v___y_2331_ = v_cd_u2081_2343_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_e_x27_2358_ = lean_ctor_get(v_a_2354_, 0);
                        lean_inc_ref_n(v_e_x27_2358_, 2);
                        v_proof_2359_ = lean_ctor_get(v_a_2354_, 1);
                        lean_inc_ref(v_proof_2359_);
                        v_done_2360_ = lean_ctor_get_uint8(
                            v_a_2354_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_contextDependent_2361_ = lean_ctor_get_uint8(
                            v_a_2354_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        lean_dec_ref_known(v_a_2354_, 2);
                        lean_inc_ref(v_e_u2081_2281_);
                        v___x_2362_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                            v_e_u2081_2281_,
                            v_e_u2082_2341_,
                            v_h_u2081_2342_,
                            v_e_x27_2358_,
                            v_proof_2359_,
                            v___y_2348_,
                            v___y_2349_,
                            v___y_2350_,
                            v___y_2351_,
                            v___y_2352_,
                        );
                        lean_dec(v___y_2352_);
                        lean_dec_ref(v___y_2351_);
                        lean_dec(v___y_2350_);
                        lean_dec_ref(v___y_2349_);
                        lean_dec(v___y_2348_);
                        if lean_obj_tag(v___x_2362_) == 0 {
                            if v_cd_u2081_2343_ == 0 {
                                v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
                                lean_inc(v_a_2363_);
                                lean_dec_ref_known(v___x_2362_, 1);
                                v___y_2334_ = v_done_2360_;
                                v___y_2335_ = v_e_x27_2358_;
                                v___y_2336_ = v_a_2363_;
                                v___y_2337_ = v___y_2346_;
                                v___y_2338_ = v_contextDependent_2361_;
                                state = 7;
                                continue;
                            } else {
                                v_a_2364_ = lean_ctor_get(v___x_2362_, 0);
                                lean_inc(v_a_2364_);
                                lean_dec_ref_known(v___x_2362_, 1);
                                v___y_2334_ = v_done_2360_;
                                v___y_2335_ = v_e_x27_2358_;
                                v___y_2336_ = v_a_2364_;
                                v___y_2337_ = v___y_2346_;
                                v___y_2338_ = v_cd_u2081_2343_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_x27_2358_);
                            lean_dec(v___y_2346_);
                            lean_dec_ref(v_e_u2081_2281_);
                            v_a_2365_ = lean_ctor_get(v___x_2362_, 0);
                            v_isSharedCheck_2372_ = (!lean_is_exclusive(v___x_2362_)) as u8;
                            if v_isSharedCheck_2372_ == 0 {
                                v___x_2367_ = v___x_2362_;
                                v_isShared_2368_ = v_isSharedCheck_2372_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2365_);
                                lean_dec(v___x_2362_);
                                v___x_2367_ = lean_box(0);
                                v_isShared_2368_ = v_isSharedCheck_2372_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___y_2352_);
                    lean_dec_ref(v___y_2351_);
                    lean_dec(v___y_2350_);
                    lean_dec_ref(v___y_2349_);
                    lean_dec(v___y_2348_);
                    lean_dec(v___y_2346_);
                    lean_dec_ref(v_h_u2081_2342_);
                    lean_dec_ref(v_e_u2082_2341_);
                    lean_dec_ref(v_e_u2081_2281_);
                    return v___x_2353_;
                }
            }
            9 => {
                if v_isShared_2368_ == 0 {
                    v___x_2370_ = v___x_2367_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
                    v___x_2370_ = v_reuseFailAlloc_2371_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2370_;
            }
            11 => {
                if lean_obj_tag(v___y_2383_) == 0 {
                    lean_dec(v___y_2382_);
                    lean_dec_ref(v___y_2381_);
                    lean_dec(v___y_2380_);
                    lean_dec(v___y_2379_);
                    lean_dec_ref(v___y_2377_);
                    lean_dec(v___y_2376_);
                    lean_dec_ref(v___y_2375_);
                    lean_dec_ref(v___y_2374_);
                    v_contextDependent_2384_ = lean_ctor_get_uint8(v___y_2383_, 1 as u32);
                    if v_contextDependent_2384_ == 0 {
                        v___x_2385_ = lean_st_ref_take(v___y_2378_);
                        v_numSteps_2386_ = lean_ctor_get(v___x_2385_, 0);
                        v_persistentCache_2387_ = lean_ctor_get(v___x_2385_, 1);
                        v_transientCache_2388_ = lean_ctor_get(v___x_2385_, 2);
                        v_funext_2389_ = lean_ctor_get(v___x_2385_, 3);
                        v_isSharedCheck_2399_ = (!lean_is_exclusive(v___x_2385_)) as u8;
                        if v_isSharedCheck_2399_ == 0 {
                            v___x_2391_ = v___x_2385_;
                            v_isShared_2392_ = v_isSharedCheck_2399_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_funext_2389_);
                            lean_inc(v_transientCache_2388_);
                            lean_inc(v_persistentCache_2387_);
                            lean_inc(v_numSteps_2386_);
                            lean_dec(v___x_2385_);
                            v___x_2391_ = lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2399_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v___x_2400_ = lean_st_ref_take(v___y_2378_);
                        v_numSteps_2401_ = lean_ctor_get(v___x_2400_, 0);
                        v_persistentCache_2402_ = lean_ctor_get(v___x_2400_, 1);
                        v_transientCache_2403_ = lean_ctor_get(v___x_2400_, 2);
                        v_funext_2404_ = lean_ctor_get(v___x_2400_, 3);
                        v_isSharedCheck_2414_ = (!lean_is_exclusive(v___x_2400_)) as u8;
                        if v_isSharedCheck_2414_ == 0 {
                            v___x_2406_ = v___x_2400_;
                            v_isShared_2407_ = v_isSharedCheck_2414_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_funext_2404_);
                            lean_inc(v_transientCache_2403_);
                            lean_inc(v_persistentCache_2402_);
                            lean_inc(v_numSteps_2401_);
                            lean_dec(v___x_2400_);
                            v___x_2406_ = lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2414_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v_done_2415_ = lean_ctor_get_uint8(
                        v___y_2383_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    if v_done_2415_ == 0 {
                        v_e_x27_2416_ = lean_ctor_get(v___y_2383_, 0);
                        lean_inc_ref(v_e_x27_2416_);
                        v_proof_2417_ = lean_ctor_get(v___y_2383_, 1);
                        lean_inc_ref(v_proof_2417_);
                        v_contextDependent_2418_ = lean_ctor_get_uint8(
                            v___y_2383_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        lean_dec_ref_known(v___y_2383_, 2);
                        v_e_u2082_2341_ = v_e_x27_2416_;
                        v_h_u2081_2342_ = v_proof_2417_;
                        v_cd_u2081_2343_ = v_contextDependent_2418_;
                        v___y_2344_ = v___y_2379_;
                        v___y_2345_ = v___y_2381_;
                        v___y_2346_ = v___y_2378_;
                        v___y_2347_ = v___y_2377_;
                        v___y_2348_ = v___y_2376_;
                        v___y_2349_ = v___y_2375_;
                        v___y_2350_ = v___y_2380_;
                        v___y_2351_ = v___y_2374_;
                        v___y_2352_ = v___y_2382_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v___y_2382_);
                        lean_dec_ref(v___y_2381_);
                        lean_dec(v___y_2380_);
                        lean_dec(v___y_2379_);
                        lean_dec_ref(v___y_2377_);
                        lean_dec(v___y_2376_);
                        lean_dec_ref(v___y_2375_);
                        lean_dec_ref(v___y_2374_);
                        v_contextDependent_2419_ = lean_ctor_get_uint8(
                            v___y_2383_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        if v_contextDependent_2419_ == 0 {
                            v___x_2420_ = lean_st_ref_take(v___y_2378_);
                            v_numSteps_2421_ = lean_ctor_get(v___x_2420_, 0);
                            v_persistentCache_2422_ = lean_ctor_get(v___x_2420_, 1);
                            v_transientCache_2423_ = lean_ctor_get(v___x_2420_, 2);
                            v_funext_2424_ = lean_ctor_get(v___x_2420_, 3);
                            v_isSharedCheck_2434_ = (!lean_is_exclusive(v___x_2420_)) as u8;
                            if v_isSharedCheck_2434_ == 0 {
                                v___x_2426_ = v___x_2420_;
                                v_isShared_2427_ = v_isSharedCheck_2434_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_funext_2424_);
                                lean_inc(v_transientCache_2423_);
                                lean_inc(v_persistentCache_2422_);
                                lean_inc(v_numSteps_2421_);
                                lean_dec(v___x_2420_);
                                v___x_2426_ = lean_box(0);
                                v_isShared_2427_ = v_isSharedCheck_2434_;
                                state = 16;
                                continue;
                            }
                        } else {
                            v___x_2435_ = lean_st_ref_take(v___y_2378_);
                            v_numSteps_2436_ = lean_ctor_get(v___x_2435_, 0);
                            v_persistentCache_2437_ = lean_ctor_get(v___x_2435_, 1);
                            v_transientCache_2438_ = lean_ctor_get(v___x_2435_, 2);
                            v_funext_2439_ = lean_ctor_get(v___x_2435_, 3);
                            v_isSharedCheck_2449_ = (!lean_is_exclusive(v___x_2435_)) as u8;
                            if v_isSharedCheck_2449_ == 0 {
                                v___x_2441_ = v___x_2435_;
                                v_isShared_2442_ = v_isSharedCheck_2449_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_funext_2439_);
                                lean_inc(v_transientCache_2438_);
                                lean_inc(v_persistentCache_2437_);
                                lean_inc(v_numSteps_2436_);
                                lean_dec(v___x_2435_);
                                v___x_2441_ = lean_box(0);
                                v_isShared_2442_ = v_isSharedCheck_2449_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            12 => {
                lean_inc_ref(v___y_2383_);
                v___x_2393_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_2387_, v_e_u2081_2281_, v___y_2383_);
                if v_isShared_2392_ == 0 {
                    lean_ctor_set(v___x_2391_, 1, v___x_2393_);
                    v___x_2395_ = v___x_2391_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_numSteps_2386_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2393_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_transientCache_2388_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_funext_2389_);
                    v___x_2395_ = v_reuseFailAlloc_2398_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2396_ = lean_st_ref_set(v___y_2378_, v___x_2395_);
                lean_dec(v___y_2378_);
                v___x_2397_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2397_, 0, v___y_2383_);
                return v___x_2397_;
            }
            14 => {
                lean_inc_ref(v___y_2383_);
                v___x_2408_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_2403_, v_e_u2081_2281_, v___y_2383_);
                if v_isShared_2407_ == 0 {
                    lean_ctor_set(v___x_2406_, 2, v___x_2408_);
                    v___x_2410_ = v___x_2406_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_numSteps_2401_);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_persistentCache_2402_);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 2, v___x_2408_);
                    lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_funext_2404_);
                    v___x_2410_ = v_reuseFailAlloc_2413_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2411_ = lean_st_ref_set(v___y_2378_, v___x_2410_);
                lean_dec(v___y_2378_);
                v___x_2412_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2412_, 0, v___y_2383_);
                return v___x_2412_;
            }
            16 => {
                lean_inc_ref(v___y_2383_);
                v___x_2428_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_2422_, v_e_u2081_2281_, v___y_2383_);
                if v_isShared_2427_ == 0 {
                    lean_ctor_set(v___x_2426_, 1, v___x_2428_);
                    v___x_2430_ = v___x_2426_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_numSteps_2421_);
                    lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2428_);
                    lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_transientCache_2423_);
                    lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_funext_2424_);
                    v___x_2430_ = v_reuseFailAlloc_2433_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2431_ = lean_st_ref_set(v___y_2378_, v___x_2430_);
                lean_dec(v___y_2378_);
                v___x_2432_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2432_, 0, v___y_2383_);
                return v___x_2432_;
            }
            18 => {
                lean_inc_ref(v___y_2383_);
                v___x_2443_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_2438_, v_e_u2081_2281_, v___y_2383_);
                if v_isShared_2442_ == 0 {
                    lean_ctor_set(v___x_2441_, 2, v___x_2443_);
                    v___x_2445_ = v___x_2441_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_numSteps_2436_);
                    lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_persistentCache_2437_);
                    lean_ctor_set(v_reuseFailAlloc_2448_, 2, v___x_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_funext_2439_);
                    v___x_2445_ = v_reuseFailAlloc_2448_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_2446_ = lean_st_ref_set(v___y_2378_, v___x_2445_);
                lean_dec(v___y_2378_);
                v___x_2447_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2447_, 0, v___y_2383_);
                return v___x_2447_;
            }
            20 => {
                if v___y_2461_ == 0 {
                    v___y_2374_ = v___y_2451_;
                    v___y_2375_ = v___y_2452_;
                    v___y_2376_ = v___y_2454_;
                    v___y_2377_ = v___y_2456_;
                    v___y_2378_ = v___y_2455_;
                    v___y_2379_ = v___y_2457_;
                    v___y_2380_ = v___y_2458_;
                    v___y_2381_ = v___y_2459_;
                    v___y_2382_ = v___y_2460_;
                    v___y_2383_ = v___y_2453_;
                    state = 11;
                    continue;
                } else {
                    v___x_2462_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2453_);
                    v___y_2374_ = v___y_2451_;
                    v___y_2375_ = v___y_2452_;
                    v___y_2376_ = v___y_2454_;
                    v___y_2377_ = v___y_2456_;
                    v___y_2378_ = v___y_2455_;
                    v___y_2379_ = v___y_2457_;
                    v___y_2380_ = v___y_2458_;
                    v___y_2381_ = v___y_2459_;
                    v___y_2382_ = v___y_2460_;
                    v___y_2383_ = v___x_2462_;
                    state = 11;
                    continue;
                }
            }
            21 => {
                if v___y_2476_ == 0 {
                    v___y_2451_ = v___y_2465_;
                    v___y_2452_ = v___y_2471_;
                    v___y_2453_ = v___y_2466_;
                    v___y_2454_ = v___y_2467_;
                    v___y_2455_ = v___y_2468_;
                    v___y_2456_ = v___y_2469_;
                    v___y_2457_ = v___y_2472_;
                    v___y_2458_ = v___y_2473_;
                    v___y_2459_ = v___y_2475_;
                    v___y_2460_ = v___y_2470_;
                    v___y_2461_ = v___y_2474_;
                    state = 20;
                    continue;
                } else {
                    v___y_2451_ = v___y_2465_;
                    v___y_2452_ = v___y_2471_;
                    v___y_2453_ = v___y_2466_;
                    v___y_2454_ = v___y_2467_;
                    v___y_2455_ = v___y_2468_;
                    v___y_2456_ = v___y_2469_;
                    v___y_2457_ = v___y_2472_;
                    v___y_2458_ = v___y_2473_;
                    v___y_2459_ = v___y_2475_;
                    v___y_2460_ = v___y_2470_;
                    v___y_2461_ = v___y_2464_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                if v___y_2486_ == 0 {
                    v___y_2374_ = v___y_2479_;
                    v___y_2375_ = v___y_2480_;
                    v___y_2376_ = v___y_2481_;
                    v___y_2377_ = v___y_2483_;
                    v___y_2378_ = v___y_2482_;
                    v___y_2379_ = v___y_2484_;
                    v___y_2380_ = v___y_2485_;
                    v___y_2381_ = v___y_2487_;
                    v___y_2382_ = v___y_2488_;
                    v___y_2383_ = v_a_2489_;
                    state = 11;
                    continue;
                } else {
                    if lean_obj_tag(v_a_2489_) == 0 {
                        v_contextDependent_2490_ = lean_ctor_get_uint8(v_a_2489_, 1 as u32);
                        v___y_2464_ = v___y_2478_;
                        v___y_2465_ = v___y_2479_;
                        v___y_2466_ = v_a_2489_;
                        v___y_2467_ = v___y_2481_;
                        v___y_2468_ = v___y_2482_;
                        v___y_2469_ = v___y_2483_;
                        v___y_2470_ = v___y_2488_;
                        v___y_2471_ = v___y_2480_;
                        v___y_2472_ = v___y_2484_;
                        v___y_2473_ = v___y_2485_;
                        v___y_2474_ = v___y_2486_;
                        v___y_2475_ = v___y_2487_;
                        v___y_2476_ = v_contextDependent_2490_;
                        state = 21;
                        continue;
                    } else {
                        v_contextDependent_2491_ = lean_ctor_get_uint8(
                            v_a_2489_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        v___y_2464_ = v___y_2478_;
                        v___y_2465_ = v___y_2479_;
                        v___y_2466_ = v_a_2489_;
                        v___y_2467_ = v___y_2481_;
                        v___y_2468_ = v___y_2482_;
                        v___y_2469_ = v___y_2483_;
                        v___y_2470_ = v___y_2488_;
                        v___y_2471_ = v___y_2480_;
                        v___y_2472_ = v___y_2484_;
                        v___y_2473_ = v___y_2485_;
                        v___y_2474_ = v___y_2486_;
                        v___y_2475_ = v___y_2487_;
                        v___y_2476_ = v_contextDependent_2491_;
                        state = 21;
                        continue;
                    }
                }
            }
            23 => {
                if lean_obj_tag(v___y_2504_) == 0 {
                    v_a_2505_ = lean_ctor_get(v___y_2504_, 0);
                    lean_inc(v_a_2505_);
                    lean_dec_ref_known(v___y_2504_, 1);
                    v___y_2478_ = v___y_2493_;
                    v___y_2479_ = v___y_2494_;
                    v___y_2480_ = v___y_2495_;
                    v___y_2481_ = v___y_2496_;
                    v___y_2482_ = v___y_2498_;
                    v___y_2483_ = v___y_2497_;
                    v___y_2484_ = v___y_2499_;
                    v___y_2485_ = v___y_2500_;
                    v___y_2486_ = v___y_2502_;
                    v___y_2487_ = v___y_2501_;
                    v___y_2488_ = v___y_2503_;
                    v_a_2489_ = v_a_2505_;
                    state = 22;
                    continue;
                } else {
                    lean_dec(v___y_2503_);
                    lean_dec_ref(v___y_2501_);
                    lean_dec(v___y_2500_);
                    lean_dec(v___y_2499_);
                    lean_dec(v___y_2498_);
                    lean_dec_ref(v___y_2497_);
                    lean_dec(v___y_2496_);
                    lean_dec_ref(v___y_2495_);
                    lean_dec_ref(v___y_2494_);
                    lean_dec_ref(v_e_u2081_2281_);
                    return v___y_2504_;
                }
            }
            24 => {
                if v___y_2519_ == 0 {
                    v___x_2520_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2518_);
                    v___y_2478_ = v___y_2507_;
                    v___y_2479_ = v___y_2508_;
                    v___y_2480_ = v___y_2513_;
                    v___y_2481_ = v___y_2509_;
                    v___y_2482_ = v___y_2510_;
                    v___y_2483_ = v___y_2511_;
                    v___y_2484_ = v___y_2514_;
                    v___y_2485_ = v___y_2515_;
                    v___y_2486_ = v___y_2516_;
                    v___y_2487_ = v___y_2517_;
                    v___y_2488_ = v___y_2512_;
                    v_a_2489_ = v___x_2520_;
                    state = 22;
                    continue;
                } else {
                    v___y_2478_ = v___y_2507_;
                    v___y_2479_ = v___y_2508_;
                    v___y_2480_ = v___y_2513_;
                    v___y_2481_ = v___y_2509_;
                    v___y_2482_ = v___y_2510_;
                    v___y_2483_ = v___y_2511_;
                    v___y_2484_ = v___y_2514_;
                    v___y_2485_ = v___y_2515_;
                    v___y_2486_ = v___y_2516_;
                    v___y_2487_ = v___y_2517_;
                    v___y_2488_ = v___y_2512_;
                    v_a_2489_ = v___y_2518_;
                    state = 22;
                    continue;
                }
            }
            25 => {
                v___x_2537_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_2537_, 0, v___y_2531_);
                lean_ctor_set(v___x_2537_, 1, v___y_2528_);
                lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_2522_,
                );
                lean_ctor_set_uint8(
                    v___x_2537_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2536_,
                );
                v___y_2478_ = v___y_2523_;
                v___y_2479_ = v___y_2524_;
                v___y_2480_ = v___y_2530_;
                v___y_2481_ = v___y_2525_;
                v___y_2482_ = v___y_2526_;
                v___y_2483_ = v___y_2527_;
                v___y_2484_ = v___y_2532_;
                v___y_2485_ = v___y_2533_;
                v___y_2486_ = v___y_2535_;
                v___y_2487_ = v___y_2534_;
                v___y_2488_ = v___y_2529_;
                v_a_2489_ = v___x_2537_;
                state = 22;
                continue;
            }
            26 => {
                v___x_2554_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_2554_, 0, v___y_2546_);
                lean_ctor_set(v___x_2554_, 1, v___y_2547_);
                lean_ctor_set_uint8(
                    v___x_2554_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_2541_,
                );
                lean_ctor_set_uint8(
                    v___x_2554_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_2553_,
                );
                v___y_2478_ = v___y_2539_;
                v___y_2479_ = v___y_2540_;
                v___y_2480_ = v___y_2548_;
                v___y_2481_ = v___y_2542_;
                v___y_2482_ = v___y_2543_;
                v___y_2483_ = v___y_2544_;
                v___y_2484_ = v___y_2549_;
                v___y_2485_ = v___y_2550_;
                v___y_2486_ = v___y_2552_;
                v___y_2487_ = v___y_2551_;
                v___y_2488_ = v___y_2545_;
                v_a_2489_ = v___x_2554_;
                state = 22;
                continue;
            }
            27 => {
                v___x_2862_ = lean_unsigned_to_nat(0);
                v___x_2863_ = lean_nat_dec_eq(v_maxRecDepth_2559_, v___x_2862_);
                if v___x_2863_ == 0 {
                    v___x_2864_ = lean_nat_dec_eq(v_currRecDepth_2558_, v_maxRecDepth_2559_);
                    if v___x_2864_ == 0 {
                        state = 65;
                        continue;
                    } else {
                        lean_del_object(v___x_2572_);
                        lean_dec_ref(v_inheritedTraceOptions_2570_);
                        lean_dec(v_cancelTk_x3f_2568_);
                        lean_dec(v_currMacroScope_2566_);
                        lean_dec(v_quotContext_2565_);
                        lean_dec(v_maxHeartbeats_2564_);
                        lean_dec(v_initHeartbeats_2563_);
                        lean_dec(v_openDecls_2562_);
                        lean_dec(v_currNamespace_2561_);
                        lean_dec(v_maxRecDepth_2559_);
                        lean_dec(v_currRecDepth_2558_);
                        lean_dec_ref(v_options_2557_);
                        lean_dec_ref(v_fileMap_2556_);
                        lean_dec_ref(v_fileName_2555_);
                        lean_dec(v_a_2290_);
                        lean_dec(v_a_2288_);
                        lean_dec_ref(v_a_2287_);
                        lean_dec(v_a_2286_);
                        lean_dec_ref(v_a_2285_);
                        lean_dec(v_a_2284_);
                        lean_dec_ref(v_a_2283_);
                        lean_dec(v_a_2282_);
                        lean_dec_ref(v_e_u2081_2281_);
                        v___x_2865_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__3___redArg(v_ref_2560_);
                        return v___x_2865_;
                    }
                } else {
                    state = 65;
                    continue;
                }
            }
            28 => {
                v___x_2585_ = lean_st_ref_take(v___y_2578_);
                v_persistentCache_2586_ = lean_ctor_get(v___x_2585_, 1);
                v_transientCache_2587_ = lean_ctor_get(v___x_2585_, 2);
                v_funext_2588_ = lean_ctor_get(v___x_2585_, 3);
                v_isSharedCheck_2713_ = (!lean_is_exclusive(v___x_2585_)) as u8;
                if v_isSharedCheck_2713_ == 0 {
                    v_unused_2714_ = lean_ctor_get(v___x_2585_, 0);
                    lean_dec(v_unused_2714_);
                    v___x_2590_ = v___x_2585_;
                    v_isShared_2591_ = v_isSharedCheck_2713_;
                    state = 29;
                    continue;
                } else {
                    lean_inc(v_funext_2588_);
                    lean_inc(v_transientCache_2587_);
                    lean_inc(v_persistentCache_2586_);
                    lean_dec(v___x_2585_);
                    v___x_2590_ = lean_box(0);
                    v_isShared_2591_ = v_isSharedCheck_2713_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_2591_ == 0 {
                    lean_ctor_set(v___x_2590_, 0, v___y_2575_);
                    v___x_2593_ = v___x_2590_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___y_2575_);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_persistentCache_2586_);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_transientCache_2587_);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_funext_2588_);
                    v___x_2593_ = v_reuseFailAlloc_2712_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2594_ = lean_st_ref_set(v___y_2578_, v___x_2593_);
                v_pre_2595_ = lean_ctor_get(v___y_2576_, 0);
                lean_inc_ref(v_pre_2595_);
                lean_inc(v___y_2584_);
                lean_inc_ref(v___y_2583_);
                lean_inc(v___y_2582_);
                lean_inc_ref(v___y_2581_);
                lean_inc(v___y_2580_);
                lean_inc_ref(v___y_2579_);
                lean_inc(v___y_2578_);
                lean_inc_ref(v___y_2577_);
                lean_inc(v___y_2576_);
                lean_inc_ref(v_e_u2081_2281_);
                v___x_2596_ = lean_apply_11(
                    v_pre_2595_,
                    v_e_u2081_2281_,
                    v___y_2576_,
                    v___y_2577_,
                    v___y_2578_,
                    v___y_2579_,
                    v___y_2580_,
                    v___y_2581_,
                    v___y_2582_,
                    v___y_2583_,
                    v___y_2584_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2596_) == 0 {
                    v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
                    v_isSharedCheck_2711_ = (!lean_is_exclusive(v___x_2596_)) as u8;
                    if v_isSharedCheck_2711_ == 0 {
                        v___x_2599_ = v___x_2596_;
                        v_isShared_2600_ = v_isSharedCheck_2711_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_2597_);
                        lean_dec(v___x_2596_);
                        v___x_2599_ = lean_box(0);
                        v_isShared_2600_ = v_isSharedCheck_2711_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2584_);
                    lean_dec_ref(v___y_2583_);
                    lean_dec(v___y_2582_);
                    lean_dec_ref(v___y_2581_);
                    lean_dec(v___y_2580_);
                    lean_dec_ref(v___y_2579_);
                    lean_dec(v___y_2578_);
                    lean_dec_ref(v___y_2577_);
                    lean_dec(v___y_2576_);
                    lean_dec_ref(v_e_u2081_2281_);
                    return v___x_2596_;
                }
            }
            31 => {
                if lean_obj_tag(v_a_2597_) == 0 {
                    v_done_2601_ = lean_ctor_get_uint8(v_a_2597_, 0 as u32);
                    if v_done_2601_ == 0 {
                        lean_del_object(v___x_2599_);
                        v_contextDependent_2602_ = lean_ctor_get_uint8(v_a_2597_, 1 as u32);
                        lean_dec_ref_known(v_a_2597_, 0);
                        lean_inc_ref(v_e_u2081_2281_);
                        v___x_2603_ =
                            l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(
                                v_e_u2081_2281_,
                                v___y_2576_,
                                v___y_2577_,
                                v___y_2578_,
                                v___y_2579_,
                                v___y_2580_,
                                v___y_2581_,
                                v___y_2582_,
                                v___y_2583_,
                                v___y_2584_,
                            );
                        if lean_obj_tag(v___x_2603_) == 0 {
                            v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
                            lean_inc(v_a_2604_);
                            v___x_2605_ = lean_box(0);
                            if lean_obj_tag(v_a_2604_) == 0 {
                                v_done_2606_ = lean_ctor_get_uint8(v_a_2604_, 0 as u32);
                                if v_done_2606_ == 0 {
                                    lean_dec_ref_known(v___x_2603_, 1);
                                    v_contextDependent_2607_ =
                                        lean_ctor_get_uint8(v_a_2604_, 1 as u32);
                                    lean_dec_ref_known(v_a_2604_, 0);
                                    lean_inc_ref(v_e_u2081_2281_);
                                    v___x_2608_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_2605_, v_e_u2081_2281_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
                                    if lean_obj_tag(v___x_2608_) == 0 {
                                        if v_contextDependent_2607_ == 0 {
                                            v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
                                            lean_inc(v_a_2609_);
                                            lean_dec_ref_known(v___x_2608_, 1);
                                            v___y_2478_ = v_done_2601_;
                                            v___y_2479_ = v___y_2583_;
                                            v___y_2480_ = v___y_2581_;
                                            v___y_2481_ = v___y_2580_;
                                            v___y_2482_ = v___y_2578_;
                                            v___y_2483_ = v___y_2579_;
                                            v___y_2484_ = v___y_2576_;
                                            v___y_2485_ = v___y_2582_;
                                            v___y_2486_ = v_contextDependent_2602_;
                                            v___y_2487_ = v___y_2577_;
                                            v___y_2488_ = v___y_2584_;
                                            v_a_2489_ = v_a_2609_;
                                            state = 22;
                                            continue;
                                        } else {
                                            v_a_2610_ = lean_ctor_get(v___x_2608_, 0);
                                            lean_inc(v_a_2610_);
                                            lean_dec_ref_known(v___x_2608_, 1);
                                            if lean_obj_tag(v_a_2610_) == 0 {
                                                v_contextDependent_2611_ =
                                                    lean_ctor_get_uint8(v_a_2610_, 1 as u32);
                                                v___y_2507_ = v_done_2601_;
                                                v___y_2508_ = v___y_2583_;
                                                v___y_2509_ = v___y_2580_;
                                                v___y_2510_ = v___y_2578_;
                                                v___y_2511_ = v___y_2579_;
                                                v___y_2512_ = v___y_2584_;
                                                v___y_2513_ = v___y_2581_;
                                                v___y_2514_ = v___y_2576_;
                                                v___y_2515_ = v___y_2582_;
                                                v___y_2516_ = v_contextDependent_2602_;
                                                v___y_2517_ = v___y_2577_;
                                                v___y_2518_ = v_a_2610_;
                                                v___y_2519_ = v_contextDependent_2611_;
                                                state = 24;
                                                continue;
                                            } else {
                                                v_contextDependent_2612_ = lean_ctor_get_uint8(
                                                    v_a_2610_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 2
                                                        + 1)
                                                        as u32,
                                                );
                                                v___y_2507_ = v_done_2601_;
                                                v___y_2508_ = v___y_2583_;
                                                v___y_2509_ = v___y_2580_;
                                                v___y_2510_ = v___y_2578_;
                                                v___y_2511_ = v___y_2579_;
                                                v___y_2512_ = v___y_2584_;
                                                v___y_2513_ = v___y_2581_;
                                                v___y_2514_ = v___y_2576_;
                                                v___y_2515_ = v___y_2582_;
                                                v___y_2516_ = v_contextDependent_2602_;
                                                v___y_2517_ = v___y_2577_;
                                                v___y_2518_ = v_a_2610_;
                                                v___y_2519_ = v_contextDependent_2612_;
                                                state = 24;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___y_2584_);
                                        lean_dec_ref(v___y_2583_);
                                        lean_dec(v___y_2582_);
                                        lean_dec_ref(v___y_2581_);
                                        lean_dec(v___y_2580_);
                                        lean_dec_ref(v___y_2579_);
                                        lean_dec(v___y_2578_);
                                        lean_dec_ref(v___y_2577_);
                                        lean_dec(v___y_2576_);
                                        lean_dec_ref(v_e_u2081_2281_);
                                        return v___x_2608_;
                                    }
                                } else {
                                    lean_dec_ref_known(v_a_2604_, 0);
                                    v___y_2493_ = v_done_2601_;
                                    v___y_2494_ = v___y_2583_;
                                    v___y_2495_ = v___y_2581_;
                                    v___y_2496_ = v___y_2580_;
                                    v___y_2497_ = v___y_2579_;
                                    v___y_2498_ = v___y_2578_;
                                    v___y_2499_ = v___y_2576_;
                                    v___y_2500_ = v___y_2582_;
                                    v___y_2501_ = v___y_2577_;
                                    v___y_2502_ = v_contextDependent_2602_;
                                    v___y_2503_ = v___y_2584_;
                                    v___y_2504_ = v___x_2603_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_done_2613_ = lean_ctor_get_uint8(
                                    v_a_2604_,
                                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                );
                                if v_done_2613_ == 0 {
                                    lean_dec_ref_known(v___x_2603_, 1);
                                    v_e_x27_2614_ = lean_ctor_get(v_a_2604_, 0);
                                    lean_inc_ref_n(v_e_x27_2614_, 2);
                                    v_proof_2615_ = lean_ctor_get(v_a_2604_, 1);
                                    lean_inc_ref(v_proof_2615_);
                                    v_contextDependent_2616_ = lean_ctor_get_uint8(
                                        v_a_2604_,
                                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                                    );
                                    lean_dec_ref_known(v_a_2604_, 2);
                                    v___x_2617_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(v___x_2605_, v_e_x27_2614_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
                                    if lean_obj_tag(v___x_2617_) == 0 {
                                        v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
                                        lean_inc(v_a_2618_);
                                        lean_dec_ref_known(v___x_2617_, 1);
                                        if lean_obj_tag(v_a_2618_) == 0 {
                                            if v_contextDependent_2616_ == 0 {
                                                v_done_2619_ =
                                                    lean_ctor_get_uint8(v_a_2618_, 0 as u32);
                                                v_contextDependent_2620_ =
                                                    lean_ctor_get_uint8(v_a_2618_, 1 as u32);
                                                lean_dec_ref_known(v_a_2618_, 0);
                                                v___y_2522_ = v_done_2619_;
                                                v___y_2523_ = v_done_2601_;
                                                v___y_2524_ = v___y_2583_;
                                                v___y_2525_ = v___y_2580_;
                                                v___y_2526_ = v___y_2578_;
                                                v___y_2527_ = v___y_2579_;
                                                v___y_2528_ = v_proof_2615_;
                                                v___y_2529_ = v___y_2584_;
                                                v___y_2530_ = v___y_2581_;
                                                v___y_2531_ = v_e_x27_2614_;
                                                v___y_2532_ = v___y_2576_;
                                                v___y_2533_ = v___y_2582_;
                                                v___y_2534_ = v___y_2577_;
                                                v___y_2535_ = v_contextDependent_2602_;
                                                v___y_2536_ = v_contextDependent_2620_;
                                                state = 25;
                                                continue;
                                            } else {
                                                v_done_2621_ =
                                                    lean_ctor_get_uint8(v_a_2618_, 0 as u32);
                                                lean_dec_ref_known(v_a_2618_, 0);
                                                v___y_2522_ = v_done_2621_;
                                                v___y_2523_ = v_done_2601_;
                                                v___y_2524_ = v___y_2583_;
                                                v___y_2525_ = v___y_2580_;
                                                v___y_2526_ = v___y_2578_;
                                                v___y_2527_ = v___y_2579_;
                                                v___y_2528_ = v_proof_2615_;
                                                v___y_2529_ = v___y_2584_;
                                                v___y_2530_ = v___y_2581_;
                                                v___y_2531_ = v_e_x27_2614_;
                                                v___y_2532_ = v___y_2576_;
                                                v___y_2533_ = v___y_2582_;
                                                v___y_2534_ = v___y_2577_;
                                                v___y_2535_ = v_contextDependent_2602_;
                                                v___y_2536_ = v_contextDependent_2616_;
                                                state = 25;
                                                continue;
                                            }
                                        } else {
                                            v_e_x27_2622_ = lean_ctor_get(v_a_2618_, 0);
                                            lean_inc_ref_n(v_e_x27_2622_, 2);
                                            v_proof_2623_ = lean_ctor_get(v_a_2618_, 1);
                                            lean_inc_ref(v_proof_2623_);
                                            v_done_2624_ = lean_ctor_get_uint8(
                                                v_a_2618_,
                                                (core::mem::size_of::<*mut LeanObject>() * 2)
                                                    as u32,
                                            );
                                            v_contextDependent_2625_ = lean_ctor_get_uint8(
                                                v_a_2618_,
                                                (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                    as u32,
                                            );
                                            lean_dec_ref_known(v_a_2618_, 2);
                                            lean_inc_ref(v_e_u2081_2281_);
                                            v___x_2626_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                                                v_e_u2081_2281_,
                                                v_e_x27_2614_,
                                                v_proof_2615_,
                                                v_e_x27_2622_,
                                                v_proof_2623_,
                                                v___y_2580_,
                                                v___y_2581_,
                                                v___y_2582_,
                                                v___y_2583_,
                                                v___y_2584_,
                                            );
                                            if lean_obj_tag(v___x_2626_) == 0 {
                                                if v_contextDependent_2616_ == 0 {
                                                    v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
                                                    lean_inc(v_a_2627_);
                                                    lean_dec_ref_known(v___x_2626_, 1);
                                                    v___y_2539_ = v_done_2601_;
                                                    v___y_2540_ = v___y_2583_;
                                                    v___y_2541_ = v_done_2624_;
                                                    v___y_2542_ = v___y_2580_;
                                                    v___y_2543_ = v___y_2578_;
                                                    v___y_2544_ = v___y_2579_;
                                                    v___y_2545_ = v___y_2584_;
                                                    v___y_2546_ = v_e_x27_2622_;
                                                    v___y_2547_ = v_a_2627_;
                                                    v___y_2548_ = v___y_2581_;
                                                    v___y_2549_ = v___y_2576_;
                                                    v___y_2550_ = v___y_2582_;
                                                    v___y_2551_ = v___y_2577_;
                                                    v___y_2552_ = v_contextDependent_2602_;
                                                    v___y_2553_ = v_contextDependent_2625_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    v_a_2628_ = lean_ctor_get(v___x_2626_, 0);
                                                    lean_inc(v_a_2628_);
                                                    lean_dec_ref_known(v___x_2626_, 1);
                                                    v___y_2539_ = v_done_2601_;
                                                    v___y_2540_ = v___y_2583_;
                                                    v___y_2541_ = v_done_2624_;
                                                    v___y_2542_ = v___y_2580_;
                                                    v___y_2543_ = v___y_2578_;
                                                    v___y_2544_ = v___y_2579_;
                                                    v___y_2545_ = v___y_2584_;
                                                    v___y_2546_ = v_e_x27_2622_;
                                                    v___y_2547_ = v_a_2628_;
                                                    v___y_2548_ = v___y_2581_;
                                                    v___y_2549_ = v___y_2576_;
                                                    v___y_2550_ = v___y_2582_;
                                                    v___y_2551_ = v___y_2577_;
                                                    v___y_2552_ = v_contextDependent_2602_;
                                                    v___y_2553_ = v_contextDependent_2616_;
                                                    state = 26;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_e_x27_2622_);
                                                lean_dec(v___y_2584_);
                                                lean_dec_ref(v___y_2583_);
                                                lean_dec(v___y_2582_);
                                                lean_dec_ref(v___y_2581_);
                                                lean_dec(v___y_2580_);
                                                lean_dec_ref(v___y_2579_);
                                                lean_dec(v___y_2578_);
                                                lean_dec_ref(v___y_2577_);
                                                lean_dec(v___y_2576_);
                                                lean_dec_ref(v_e_u2081_2281_);
                                                v_a_2629_ = lean_ctor_get(v___x_2626_, 0);
                                                v_isSharedCheck_2636_ =
                                                    (!lean_is_exclusive(v___x_2626_)) as u8;
                                                if v_isSharedCheck_2636_ == 0 {
                                                    v___x_2631_ = v___x_2626_;
                                                    v_isShared_2632_ = v_isSharedCheck_2636_;
                                                    state = 32;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2629_);
                                                    lean_dec(v___x_2626_);
                                                    v___x_2631_ = lean_box(0);
                                                    v_isShared_2632_ = v_isSharedCheck_2636_;
                                                    state = 32;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_proof_2615_);
                                        lean_dec_ref(v_e_x27_2614_);
                                        lean_dec(v___y_2584_);
                                        lean_dec_ref(v___y_2583_);
                                        lean_dec(v___y_2582_);
                                        lean_dec_ref(v___y_2581_);
                                        lean_dec(v___y_2580_);
                                        lean_dec_ref(v___y_2579_);
                                        lean_dec(v___y_2578_);
                                        lean_dec_ref(v___y_2577_);
                                        lean_dec(v___y_2576_);
                                        lean_dec_ref(v_e_u2081_2281_);
                                        return v___x_2617_;
                                    }
                                } else {
                                    lean_dec_ref_known(v_a_2604_, 2);
                                    v___y_2493_ = v_done_2601_;
                                    v___y_2494_ = v___y_2583_;
                                    v___y_2495_ = v___y_2581_;
                                    v___y_2496_ = v___y_2580_;
                                    v___y_2497_ = v___y_2579_;
                                    v___y_2498_ = v___y_2578_;
                                    v___y_2499_ = v___y_2576_;
                                    v___y_2500_ = v___y_2582_;
                                    v___y_2501_ = v___y_2577_;
                                    v___y_2502_ = v_contextDependent_2602_;
                                    v___y_2503_ = v___y_2584_;
                                    v___y_2504_ = v___x_2603_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            v___y_2493_ = v_done_2601_;
                            v___y_2494_ = v___y_2583_;
                            v___y_2495_ = v___y_2581_;
                            v___y_2496_ = v___y_2580_;
                            v___y_2497_ = v___y_2579_;
                            v___y_2498_ = v___y_2578_;
                            v___y_2499_ = v___y_2576_;
                            v___y_2500_ = v___y_2582_;
                            v___y_2501_ = v___y_2577_;
                            v___y_2502_ = v_contextDependent_2602_;
                            v___y_2503_ = v___y_2584_;
                            v___y_2504_ = v___x_2603_;
                            state = 23;
                            continue;
                        }
                    } else {
                        lean_dec(v___y_2584_);
                        lean_dec_ref(v___y_2583_);
                        lean_dec(v___y_2582_);
                        lean_dec_ref(v___y_2581_);
                        lean_dec(v___y_2580_);
                        lean_dec_ref(v___y_2579_);
                        lean_dec_ref(v___y_2577_);
                        lean_dec(v___y_2576_);
                        v_contextDependent_2637_ = lean_ctor_get_uint8(v_a_2597_, 1 as u32);
                        if v_contextDependent_2637_ == 0 {
                            v___x_2638_ = lean_st_ref_take(v___y_2578_);
                            v_numSteps_2639_ = lean_ctor_get(v___x_2638_, 0);
                            v_persistentCache_2640_ = lean_ctor_get(v___x_2638_, 1);
                            v_transientCache_2641_ = lean_ctor_get(v___x_2638_, 2);
                            v_funext_2642_ = lean_ctor_get(v___x_2638_, 3);
                            v_isSharedCheck_2654_ = (!lean_is_exclusive(v___x_2638_)) as u8;
                            if v_isSharedCheck_2654_ == 0 {
                                v___x_2644_ = v___x_2638_;
                                v_isShared_2645_ = v_isSharedCheck_2654_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_funext_2642_);
                                lean_inc(v_transientCache_2641_);
                                lean_inc(v_persistentCache_2640_);
                                lean_inc(v_numSteps_2639_);
                                lean_dec(v___x_2638_);
                                v___x_2644_ = lean_box(0);
                                v_isShared_2645_ = v_isSharedCheck_2654_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v___x_2655_ = lean_st_ref_take(v___y_2578_);
                            v_numSteps_2656_ = lean_ctor_get(v___x_2655_, 0);
                            v_persistentCache_2657_ = lean_ctor_get(v___x_2655_, 1);
                            v_transientCache_2658_ = lean_ctor_get(v___x_2655_, 2);
                            v_funext_2659_ = lean_ctor_get(v___x_2655_, 3);
                            v_isSharedCheck_2671_ = (!lean_is_exclusive(v___x_2655_)) as u8;
                            if v_isSharedCheck_2671_ == 0 {
                                v___x_2661_ = v___x_2655_;
                                v_isShared_2662_ = v_isSharedCheck_2671_;
                                state = 37;
                                continue;
                            } else {
                                lean_inc(v_funext_2659_);
                                lean_inc(v_transientCache_2658_);
                                lean_inc(v_persistentCache_2657_);
                                lean_inc(v_numSteps_2656_);
                                lean_dec(v___x_2655_);
                                v___x_2661_ = lean_box(0);
                                v_isShared_2662_ = v_isSharedCheck_2671_;
                                state = 37;
                                continue;
                            }
                        }
                    }
                } else {
                    v_done_2672_ = lean_ctor_get_uint8(
                        v_a_2597_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    if v_done_2672_ == 0 {
                        lean_del_object(v___x_2599_);
                        v_e_x27_2673_ = lean_ctor_get(v_a_2597_, 0);
                        lean_inc_ref(v_e_x27_2673_);
                        v_proof_2674_ = lean_ctor_get(v_a_2597_, 1);
                        lean_inc_ref(v_proof_2674_);
                        v_contextDependent_2675_ = lean_ctor_get_uint8(
                            v_a_2597_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        lean_dec_ref_known(v_a_2597_, 2);
                        v_e_u2082_2341_ = v_e_x27_2673_;
                        v_h_u2081_2342_ = v_proof_2674_;
                        v_cd_u2081_2343_ = v_contextDependent_2675_;
                        v___y_2344_ = v___y_2576_;
                        v___y_2345_ = v___y_2577_;
                        v___y_2346_ = v___y_2578_;
                        v___y_2347_ = v___y_2579_;
                        v___y_2348_ = v___y_2580_;
                        v___y_2349_ = v___y_2581_;
                        v___y_2350_ = v___y_2582_;
                        v___y_2351_ = v___y_2583_;
                        v___y_2352_ = v___y_2584_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v___y_2584_);
                        lean_dec_ref(v___y_2583_);
                        lean_dec(v___y_2582_);
                        lean_dec_ref(v___y_2581_);
                        lean_dec(v___y_2580_);
                        lean_dec_ref(v___y_2579_);
                        lean_dec_ref(v___y_2577_);
                        lean_dec(v___y_2576_);
                        v_contextDependent_2676_ = lean_ctor_get_uint8(
                            v_a_2597_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        );
                        if v_contextDependent_2676_ == 0 {
                            v___x_2677_ = lean_st_ref_take(v___y_2578_);
                            v_numSteps_2678_ = lean_ctor_get(v___x_2677_, 0);
                            v_persistentCache_2679_ = lean_ctor_get(v___x_2677_, 1);
                            v_transientCache_2680_ = lean_ctor_get(v___x_2677_, 2);
                            v_funext_2681_ = lean_ctor_get(v___x_2677_, 3);
                            v_isSharedCheck_2693_ = (!lean_is_exclusive(v___x_2677_)) as u8;
                            if v_isSharedCheck_2693_ == 0 {
                                v___x_2683_ = v___x_2677_;
                                v_isShared_2684_ = v_isSharedCheck_2693_;
                                state = 40;
                                continue;
                            } else {
                                lean_inc(v_funext_2681_);
                                lean_inc(v_transientCache_2680_);
                                lean_inc(v_persistentCache_2679_);
                                lean_inc(v_numSteps_2678_);
                                lean_dec(v___x_2677_);
                                v___x_2683_ = lean_box(0);
                                v_isShared_2684_ = v_isSharedCheck_2693_;
                                state = 40;
                                continue;
                            }
                        } else {
                            v___x_2694_ = lean_st_ref_take(v___y_2578_);
                            v_numSteps_2695_ = lean_ctor_get(v___x_2694_, 0);
                            v_persistentCache_2696_ = lean_ctor_get(v___x_2694_, 1);
                            v_transientCache_2697_ = lean_ctor_get(v___x_2694_, 2);
                            v_funext_2698_ = lean_ctor_get(v___x_2694_, 3);
                            v_isSharedCheck_2710_ = (!lean_is_exclusive(v___x_2694_)) as u8;
                            if v_isSharedCheck_2710_ == 0 {
                                v___x_2700_ = v___x_2694_;
                                v_isShared_2701_ = v_isSharedCheck_2710_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_funext_2698_);
                                lean_inc(v_transientCache_2697_);
                                lean_inc(v_persistentCache_2696_);
                                lean_inc(v_numSteps_2695_);
                                lean_dec(v___x_2694_);
                                v___x_2700_ = lean_box(0);
                                v_isShared_2701_ = v_isSharedCheck_2710_;
                                state = 43;
                                continue;
                            }
                        }
                    }
                }
            }
            32 => {
                if v_isShared_2632_ == 0 {
                    v___x_2634_ = v___x_2631_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
                    v___x_2634_ = v_reuseFailAlloc_2635_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2634_;
            }
            34 => {
                lean_inc_ref(v_a_2597_);
                v___x_2646_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_2640_, v_e_u2081_2281_, v_a_2597_);
                if v_isShared_2645_ == 0 {
                    lean_ctor_set(v___x_2644_, 1, v___x_2646_);
                    v___x_2648_ = v___x_2644_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_numSteps_2639_);
                    lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2646_);
                    lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_transientCache_2641_);
                    lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_funext_2642_);
                    v___x_2648_ = v_reuseFailAlloc_2653_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2649_ = lean_st_ref_set(v___y_2578_, v___x_2648_);
                lean_dec(v___y_2578_);
                if v_isShared_2600_ == 0 {
                    v___x_2651_ = v___x_2599_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2597_);
                    v___x_2651_ = v_reuseFailAlloc_2652_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2651_;
            }
            37 => {
                lean_inc_ref(v_a_2597_);
                v___x_2663_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_2658_, v_e_u2081_2281_, v_a_2597_);
                if v_isShared_2662_ == 0 {
                    lean_ctor_set(v___x_2661_, 2, v___x_2663_);
                    v___x_2665_ = v___x_2661_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_numSteps_2656_);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_persistentCache_2657_);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 2, v___x_2663_);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_funext_2659_);
                    v___x_2665_ = v_reuseFailAlloc_2670_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_2666_ = lean_st_ref_set(v___y_2578_, v___x_2665_);
                lean_dec(v___y_2578_);
                if v_isShared_2600_ == 0 {
                    v___x_2668_ = v___x_2599_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2597_);
                    v___x_2668_ = v_reuseFailAlloc_2669_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2668_;
            }
            40 => {
                lean_inc_ref(v_a_2597_);
                v___x_2685_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_persistentCache_2679_, v_e_u2081_2281_, v_a_2597_);
                if v_isShared_2684_ == 0 {
                    lean_ctor_set(v___x_2683_, 1, v___x_2685_);
                    v___x_2687_ = v___x_2683_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_numSteps_2678_);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2685_);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_transientCache_2680_);
                    lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_funext_2681_);
                    v___x_2687_ = v_reuseFailAlloc_2692_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___x_2688_ = lean_st_ref_set(v___y_2578_, v___x_2687_);
                lean_dec(v___y_2578_);
                if v_isShared_2600_ == 0 {
                    v___x_2690_ = v___x_2599_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2597_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2690_;
            }
            43 => {
                lean_inc_ref(v_a_2597_);
                v___x_2702_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_transientCache_2697_, v_e_u2081_2281_, v_a_2597_);
                if v_isShared_2701_ == 0 {
                    lean_ctor_set(v___x_2700_, 2, v___x_2702_);
                    v___x_2704_ = v___x_2700_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_numSteps_2695_);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_persistentCache_2696_);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 2, v___x_2702_);
                    lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_funext_2698_);
                    v___x_2704_ = v_reuseFailAlloc_2709_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_2705_ = lean_st_ref_set(v___y_2578_, v___x_2704_);
                lean_dec(v___y_2578_);
                if v_isShared_2600_ == 0 {
                    v___x_2707_ = v___x_2599_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2597_);
                    v___x_2707_ = v_reuseFailAlloc_2708_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_2707_;
            }
            46 => {
                v___x_2727_ = lean_st_ref_get(v___y_2720_);
                v_persistentCache_2728_ = lean_ctor_get(v___x_2727_, 1);
                lean_inc_ref(v_persistentCache_2728_);
                lean_dec(v___x_2727_);
                v___x_2729_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_persistentCache_2728_, v_e_u2081_2281_);
                lean_dec_ref(v_persistentCache_2728_);
                if lean_obj_tag(v___x_2729_) == 1 {
                    lean_dec(v___y_2722_);
                    lean_dec_ref(v___y_2721_);
                    lean_dec(v___y_2720_);
                    lean_dec_ref(v___y_2719_);
                    lean_dec(v___y_2718_);
                    lean_dec(v___y_2717_);
                    v_options_2730_ = lean_ctor_get(v___y_2725_, 2);
                    v_hasTrace_2731_ = lean_ctor_get_uint8(
                        v_options_2730_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2731_ == 0 {
                        lean_dec(v___y_2726_);
                        lean_dec_ref(v___y_2725_);
                        lean_dec(v___y_2724_);
                        lean_dec_ref(v___y_2723_);
                        lean_dec_ref(v_e_u2081_2281_);
                        v_val_2732_ = lean_ctor_get(v___x_2729_, 0);
                        v_isSharedCheck_2739_ = (!lean_is_exclusive(v___x_2729_)) as u8;
                        if v_isSharedCheck_2739_ == 0 {
                            v___x_2734_ = v___x_2729_;
                            v_isShared_2735_ = v_isSharedCheck_2739_;
                            state = 47;
                            continue;
                        } else {
                            lean_inc(v_val_2732_);
                            lean_dec(v___x_2729_);
                            v___x_2734_ = lean_box(0);
                            v_isShared_2735_ = v_isSharedCheck_2739_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_val_2740_ = lean_ctor_get(v___x_2729_, 0);
                        v_isSharedCheck_2771_ = (!lean_is_exclusive(v___x_2729_)) as u8;
                        if v_isSharedCheck_2771_ == 0 {
                            v___x_2742_ = v___x_2729_;
                            v_isShared_2743_ = v_isSharedCheck_2771_;
                            state = 49;
                            continue;
                        } else {
                            lean_inc(v_val_2740_);
                            lean_dec(v___x_2729_);
                            v___x_2742_ = lean_box(0);
                            v_isShared_2743_ = v_isSharedCheck_2771_;
                            state = 49;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2729_);
                    v___x_2772_ = lean_st_ref_get(v___y_2720_);
                    v_transientCache_2773_ = lean_ctor_get(v___x_2772_, 2);
                    lean_inc_ref(v_transientCache_2773_);
                    lean_dec(v___x_2772_);
                    v___x_2774_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_transientCache_2773_, v_e_u2081_2281_);
                    lean_dec_ref(v_transientCache_2773_);
                    if lean_obj_tag(v___x_2774_) == 1 {
                        lean_dec(v___y_2722_);
                        lean_dec_ref(v___y_2721_);
                        lean_dec(v___y_2720_);
                        lean_dec_ref(v___y_2719_);
                        lean_dec(v___y_2718_);
                        lean_dec(v___y_2717_);
                        v_options_2775_ = lean_ctor_get(v___y_2725_, 2);
                        v_hasTrace_2776_ = lean_ctor_get_uint8(
                            v_options_2775_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2776_ == 0 {
                            lean_dec(v___y_2726_);
                            lean_dec_ref(v___y_2725_);
                            lean_dec(v___y_2724_);
                            lean_dec_ref(v___y_2723_);
                            lean_dec_ref(v_e_u2081_2281_);
                            v_val_2777_ = lean_ctor_get(v___x_2774_, 0);
                            v_isSharedCheck_2784_ = (!lean_is_exclusive(v___x_2774_)) as u8;
                            if v_isSharedCheck_2784_ == 0 {
                                v___x_2779_ = v___x_2774_;
                                v_isShared_2780_ = v_isSharedCheck_2784_;
                                state = 55;
                                continue;
                            } else {
                                lean_inc(v_val_2777_);
                                lean_dec(v___x_2774_);
                                v___x_2779_ = lean_box(0);
                                v_isShared_2780_ = v_isSharedCheck_2784_;
                                state = 55;
                                continue;
                            }
                        } else {
                            v_val_2785_ = lean_ctor_get(v___x_2774_, 0);
                            v_isSharedCheck_2816_ = (!lean_is_exclusive(v___x_2774_)) as u8;
                            if v_isSharedCheck_2816_ == 0 {
                                v___x_2787_ = v___x_2774_;
                                v_isShared_2788_ = v_isSharedCheck_2816_;
                                state = 57;
                                continue;
                            } else {
                                lean_inc(v_val_2785_);
                                lean_dec(v___x_2774_);
                                v___x_2787_ = lean_box(0);
                                v_isShared_2788_ = v_isSharedCheck_2816_;
                                state = 57;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2774_);
                        v___x_2817_ = lean_nat_add(v___y_2717_, v___y_2716_);
                        lean_dec(v___y_2717_);
                        v___x_2818_ = lean_unsigned_to_nat(1000);
                        v___x_2819_ = lean_nat_mod(v___x_2817_, v___x_2818_);
                        v___x_2820_ = lean_unsigned_to_nat(0);
                        v___x_2821_ = lean_nat_dec_eq(v___x_2819_, v___x_2820_);
                        lean_dec(v___x_2819_);
                        if v___x_2821_ == 0 {
                            v___y_2575_ = v___x_2817_;
                            v___y_2576_ = v___y_2718_;
                            v___y_2577_ = v___y_2719_;
                            v___y_2578_ = v___y_2720_;
                            v___y_2579_ = v___y_2721_;
                            v___y_2580_ = v___y_2722_;
                            v___y_2581_ = v___y_2723_;
                            v___y_2582_ = v___y_2724_;
                            v___y_2583_ = v___y_2725_;
                            v___y_2584_ = v___y_2726_;
                            state = 28;
                            continue;
                        } else {
                            v___x_2822_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
                            v___x_2823_ =
                                l_Lean_Core_checkSystem(v___x_2822_, v___y_2725_, v___y_2726_);
                            if lean_obj_tag(v___x_2823_) == 0 {
                                lean_dec_ref_known(v___x_2823_, 1);
                                v___y_2575_ = v___x_2817_;
                                v___y_2576_ = v___y_2718_;
                                v___y_2577_ = v___y_2719_;
                                v___y_2578_ = v___y_2720_;
                                v___y_2579_ = v___y_2721_;
                                v___y_2580_ = v___y_2722_;
                                v___y_2581_ = v___y_2723_;
                                v___y_2582_ = v___y_2724_;
                                v___y_2583_ = v___y_2725_;
                                v___y_2584_ = v___y_2726_;
                                state = 28;
                                continue;
                            } else {
                                lean_dec(v___x_2817_);
                                lean_dec(v___y_2726_);
                                lean_dec_ref(v___y_2725_);
                                lean_dec(v___y_2724_);
                                lean_dec_ref(v___y_2723_);
                                lean_dec(v___y_2722_);
                                lean_dec_ref(v___y_2721_);
                                lean_dec(v___y_2720_);
                                lean_dec_ref(v___y_2719_);
                                lean_dec(v___y_2718_);
                                lean_dec_ref(v_e_u2081_2281_);
                                v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
                                v_isSharedCheck_2831_ = (!lean_is_exclusive(v___x_2823_)) as u8;
                                if v_isSharedCheck_2831_ == 0 {
                                    v___x_2826_ = v___x_2823_;
                                    v_isShared_2827_ = v_isSharedCheck_2831_;
                                    state = 63;
                                    continue;
                                } else {
                                    lean_inc(v_a_2824_);
                                    lean_dec(v___x_2823_);
                                    v___x_2826_ = lean_box(0);
                                    v_isShared_2827_ = v_isSharedCheck_2831_;
                                    state = 63;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            47 => {
                if v_isShared_2735_ == 0 {
                    lean_ctor_set_tag(v___x_2734_, 0);
                    v___x_2737_ = v___x_2734_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_val_2732_);
                    v___x_2737_ = v_reuseFailAlloc_2738_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2737_;
            }
            49 => {
                v_inheritedTraceOptions_2744_ = lean_ctor_get(v___y_2725_, 13);
                v___x_2745_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
                v___x_2746_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
                v___x_2747_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_2744_,
                    v_options_2730_,
                    v___x_2746_,
                );
                if v___x_2747_ == 0 {
                    lean_dec(v___y_2726_);
                    lean_dec_ref(v___y_2725_);
                    lean_dec(v___y_2724_);
                    lean_dec_ref(v___y_2723_);
                    lean_dec_ref(v_e_u2081_2281_);
                    if v_isShared_2743_ == 0 {
                        lean_ctor_set_tag(v___x_2742_, 0);
                        v___x_2749_ = v___x_2742_;
                        state = 50;
                        continue;
                    } else {
                        v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_val_2740_);
                        v___x_2749_ = v_reuseFailAlloc_2750_;
                        state = 50;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2742_);
                    v___x_2751_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__4);
                    v___x_2752_ = l_Lean_MessageData_ofExpr(v_e_u2081_2281_);
                    v___x_2753_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2753_, 0, v___x_2751_);
                    lean_ctor_set(v___x_2753_, 1, v___x_2752_);
                    v___x_2754_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_2745_, v___x_2753_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
                    lean_dec(v___y_2726_);
                    lean_dec_ref(v___y_2725_);
                    lean_dec(v___y_2724_);
                    lean_dec_ref(v___y_2723_);
                    if lean_obj_tag(v___x_2754_) == 0 {
                        v_isSharedCheck_2761_ = (!lean_is_exclusive(v___x_2754_)) as u8;
                        if v_isSharedCheck_2761_ == 0 {
                            v_unused_2762_ = lean_ctor_get(v___x_2754_, 0);
                            lean_dec(v_unused_2762_);
                            v___x_2756_ = v___x_2754_;
                            v_isShared_2757_ = v_isSharedCheck_2761_;
                            state = 51;
                            continue;
                        } else {
                            lean_dec(v___x_2754_);
                            v___x_2756_ = lean_box(0);
                            v_isShared_2757_ = v_isSharedCheck_2761_;
                            state = 51;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2740_);
                        v_a_2763_ = lean_ctor_get(v___x_2754_, 0);
                        v_isSharedCheck_2770_ = (!lean_is_exclusive(v___x_2754_)) as u8;
                        if v_isSharedCheck_2770_ == 0 {
                            v___x_2765_ = v___x_2754_;
                            v_isShared_2766_ = v_isSharedCheck_2770_;
                            state = 53;
                            continue;
                        } else {
                            lean_inc(v_a_2763_);
                            lean_dec(v___x_2754_);
                            v___x_2765_ = lean_box(0);
                            v_isShared_2766_ = v_isSharedCheck_2770_;
                            state = 53;
                            continue;
                        }
                    }
                }
            }
            50 => {
                return v___x_2749_;
            }
            51 => {
                if v_isShared_2757_ == 0 {
                    lean_ctor_set(v___x_2756_, 0, v_val_2740_);
                    v___x_2759_ = v___x_2756_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_val_2740_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_2759_;
            }
            53 => {
                if v_isShared_2766_ == 0 {
                    v___x_2768_ = v___x_2765_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
                    v___x_2768_ = v_reuseFailAlloc_2769_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_2768_;
            }
            55 => {
                if v_isShared_2780_ == 0 {
                    lean_ctor_set_tag(v___x_2779_, 0);
                    v___x_2782_ = v___x_2779_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_val_2777_);
                    v___x_2782_ = v_reuseFailAlloc_2783_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_2782_;
            }
            57 => {
                v_inheritedTraceOptions_2789_ = lean_ctor_get(v___y_2725_, 13);
                v___x_2790_ = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_;
                v___x_2791_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
                v___x_2792_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_2789_,
                    v_options_2775_,
                    v___x_2791_,
                );
                if v___x_2792_ == 0 {
                    lean_dec(v___y_2726_);
                    lean_dec_ref(v___y_2725_);
                    lean_dec(v___y_2724_);
                    lean_dec_ref(v___y_2723_);
                    lean_dec_ref(v_e_u2081_2281_);
                    if v_isShared_2788_ == 0 {
                        lean_ctor_set_tag(v___x_2787_, 0);
                        v___x_2794_ = v___x_2787_;
                        state = 58;
                        continue;
                    } else {
                        v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_val_2785_);
                        v___x_2794_ = v_reuseFailAlloc_2795_;
                        state = 58;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2787_);
                    v___x_2796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__6);
                    v___x_2797_ = l_Lean_MessageData_ofExpr(v_e_u2081_2281_);
                    v___x_2798_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2798_, 0, v___x_2796_);
                    lean_ctor_set(v___x_2798_, 1, v___x_2797_);
                    v___x_2799_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v___x_2790_, v___x_2798_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
                    lean_dec(v___y_2726_);
                    lean_dec_ref(v___y_2725_);
                    lean_dec(v___y_2724_);
                    lean_dec_ref(v___y_2723_);
                    if lean_obj_tag(v___x_2799_) == 0 {
                        v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2799_)) as u8;
                        if v_isSharedCheck_2806_ == 0 {
                            v_unused_2807_ = lean_ctor_get(v___x_2799_, 0);
                            lean_dec(v_unused_2807_);
                            v___x_2801_ = v___x_2799_;
                            v_isShared_2802_ = v_isSharedCheck_2806_;
                            state = 59;
                            continue;
                        } else {
                            lean_dec(v___x_2799_);
                            v___x_2801_ = lean_box(0);
                            v_isShared_2802_ = v_isSharedCheck_2806_;
                            state = 59;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2785_);
                        v_a_2808_ = lean_ctor_get(v___x_2799_, 0);
                        v_isSharedCheck_2815_ = (!lean_is_exclusive(v___x_2799_)) as u8;
                        if v_isSharedCheck_2815_ == 0 {
                            v___x_2810_ = v___x_2799_;
                            v_isShared_2811_ = v_isSharedCheck_2815_;
                            state = 61;
                            continue;
                        } else {
                            lean_inc(v_a_2808_);
                            lean_dec(v___x_2799_);
                            v___x_2810_ = lean_box(0);
                            v_isShared_2811_ = v_isSharedCheck_2815_;
                            state = 61;
                            continue;
                        }
                    }
                }
            }
            58 => {
                return v___x_2794_;
            }
            59 => {
                if v_isShared_2802_ == 0 {
                    lean_ctor_set(v___x_2801_, 0, v_val_2785_);
                    v___x_2804_ = v___x_2801_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_val_2785_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2804_;
            }
            61 => {
                if v_isShared_2811_ == 0 {
                    v___x_2813_ = v___x_2810_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
                    v___x_2813_ = v_reuseFailAlloc_2814_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2813_;
            }
            63 => {
                if v_isShared_2827_ == 0 {
                    v___x_2829_ = v___x_2826_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
                    v___x_2829_ = v_reuseFailAlloc_2830_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_2829_;
            }
            65 => {
                v___x_2833_ = lean_st_ref_get(v_a_2284_);
                v___x_2834_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_2283_);
                if lean_obj_tag(v___x_2834_) == 0 {
                    v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
                    lean_inc(v_a_2835_);
                    lean_dec_ref_known(v___x_2834_, 1);
                    v_numSteps_2836_ = lean_ctor_get(v___x_2833_, 0);
                    lean_inc(v_numSteps_2836_);
                    lean_dec(v___x_2833_);
                    v_maxSteps_2837_ = lean_ctor_get(v_a_2835_, 0);
                    lean_inc(v_maxSteps_2837_);
                    lean_dec(v_a_2835_);
                    v___x_2838_ = lean_unsigned_to_nat(1);
                    v___x_2839_ = lean_nat_add(v_currRecDepth_2558_, v___x_2838_);
                    lean_dec(v_currRecDepth_2558_);
                    if v_isShared_2573_ == 0 {
                        lean_ctor_set(v___x_2572_, 3, v___x_2839_);
                        v___x_2841_ = v___x_2572_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 14, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_fileName_2555_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_fileMap_2556_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_options_2557_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 3, v___x_2839_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_maxRecDepth_2559_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 5, v_ref_2560_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 6, v_currNamespace_2561_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 7, v_openDecls_2562_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 8, v_initHeartbeats_2563_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 9, v_maxHeartbeats_2564_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 10, v_quotContext_2565_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 11, v_currMacroScope_2566_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 12, v_cancelTk_x3f_2568_);
                        lean_ctor_set(v_reuseFailAlloc_2853_, 13, v_inheritedTraceOptions_2570_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2853_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                            v_diag_2567_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2853_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_2569_,
                        );
                        v___x_2841_ = v_reuseFailAlloc_2853_;
                        state = 66;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2833_);
                    lean_del_object(v___x_2572_);
                    lean_dec_ref(v_inheritedTraceOptions_2570_);
                    lean_dec(v_cancelTk_x3f_2568_);
                    lean_dec(v_currMacroScope_2566_);
                    lean_dec(v_quotContext_2565_);
                    lean_dec(v_maxHeartbeats_2564_);
                    lean_dec(v_initHeartbeats_2563_);
                    lean_dec(v_openDecls_2562_);
                    lean_dec(v_currNamespace_2561_);
                    lean_dec(v_ref_2560_);
                    lean_dec(v_maxRecDepth_2559_);
                    lean_dec(v_currRecDepth_2558_);
                    lean_dec_ref(v_options_2557_);
                    lean_dec_ref(v_fileMap_2556_);
                    lean_dec_ref(v_fileName_2555_);
                    lean_dec(v_a_2290_);
                    lean_dec(v_a_2288_);
                    lean_dec_ref(v_a_2287_);
                    lean_dec(v_a_2286_);
                    lean_dec_ref(v_a_2285_);
                    lean_dec(v_a_2284_);
                    lean_dec_ref(v_a_2283_);
                    lean_dec(v_a_2282_);
                    lean_dec_ref(v_e_u2081_2281_);
                    v_a_2854_ = lean_ctor_get(v___x_2834_, 0);
                    v_isSharedCheck_2861_ = (!lean_is_exclusive(v___x_2834_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2856_ = v___x_2834_;
                        v_isShared_2857_ = v_isSharedCheck_2861_;
                        state = 69;
                        continue;
                    } else {
                        lean_inc(v_a_2854_);
                        lean_dec(v___x_2834_);
                        v___x_2856_ = lean_box(0);
                        v_isShared_2857_ = v_isSharedCheck_2861_;
                        state = 69;
                        continue;
                    }
                }
            }
            66 => {
                v___x_2842_ = lean_nat_dec_le(v_maxSteps_2837_, v_numSteps_2836_);
                lean_dec(v_maxSteps_2837_);
                if v___x_2842_ == 0 {
                    v___y_2716_ = v___x_2838_;
                    v___y_2717_ = v_numSteps_2836_;
                    v___y_2718_ = v_a_2282_;
                    v___y_2719_ = v_a_2283_;
                    v___y_2720_ = v_a_2284_;
                    v___y_2721_ = v_a_2285_;
                    v___y_2722_ = v_a_2286_;
                    v___y_2723_ = v_a_2287_;
                    v___y_2724_ = v_a_2288_;
                    v___y_2725_ = v___x_2841_;
                    v___y_2726_ = v_a_2290_;
                    state = 46;
                    continue;
                } else {
                    lean_dec(v_numSteps_2836_);
                    lean_dec(v_a_2286_);
                    lean_dec_ref(v_a_2285_);
                    lean_dec(v_a_2284_);
                    lean_dec_ref(v_a_2283_);
                    lean_dec(v_a_2282_);
                    lean_dec_ref(v_e_u2081_2281_);
                    v___x_2843_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8_once), _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__8);
                    v___x_2844_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(v___x_2843_, v_a_2287_, v_a_2288_, v___x_2841_, v_a_2290_);
                    lean_dec(v_a_2290_);
                    lean_dec_ref(v___x_2841_);
                    lean_dec(v_a_2288_);
                    lean_dec_ref(v_a_2287_);
                    v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
                    v_isSharedCheck_2852_ = (!lean_is_exclusive(v___x_2844_)) as u8;
                    if v_isSharedCheck_2852_ == 0 {
                        v___x_2847_ = v___x_2844_;
                        v_isShared_2848_ = v_isSharedCheck_2852_;
                        state = 67;
                        continue;
                    } else {
                        lean_inc(v_a_2845_);
                        lean_dec(v___x_2844_);
                        v___x_2847_ = lean_box(0);
                        v_isShared_2848_ = v_isSharedCheck_2852_;
                        state = 67;
                        continue;
                    }
                }
            }
            67 => {
                if v_isShared_2848_ == 0 {
                    v___x_2850_ = v___x_2847_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
                    v___x_2850_ = v_reuseFailAlloc_2851_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_2850_;
            }
            69 => {
                if v_isShared_2857_ == 0 {
                    v___x_2859_ = v___x_2856_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
                    v___x_2859_ = v_reuseFailAlloc_2860_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_2859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(
    mut v_e_u2081_2867_: *mut LeanObject,
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
    v_res_2878_ = lean_sym_simp(
        v_e_u2081_2867_,
        v_a_2868_,
        v_a_2869_,
        v_a_2870_,
        v_a_2871_,
        v_a_2872_,
        v_a_2873_,
        v_a_2874_,
        v_a_2875_,
        v_a_2876_,
    );
    return v_res_2878_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(
    mut v_00_u03b2_2879_: *mut LeanObject,
    mut v_x_2880_: *mut LeanObject,
    mut v_x_2881_: *mut LeanObject,
    mut v_x_2882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    v___x_2883_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(v_x_2880_, v_x_2881_, v_x_2882_);
    return v___x_2883_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(
    mut v_00_u03b2_2884_: *mut LeanObject,
    mut v_x_2885_: *mut LeanObject,
    mut v_x_2886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    v___x_2887_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(v_x_2885_, v_x_2886_);
    return v___x_2887_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(
    mut v_00_u03b2_2888_: *mut LeanObject,
    mut v_x_2889_: *mut LeanObject,
    mut v_x_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2891_: *mut LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(v_00_u03b2_2888_, v_x_2889_, v_x_2890_);
    lean_dec_ref(v_x_2890_);
    lean_dec_ref(v_x_2889_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(
    mut v_cls_2892_: *mut LeanObject,
    mut v_msg_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
    mut v___y_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
    mut v___y_2898_: *mut LeanObject,
    mut v___y_2899_: *mut LeanObject,
    mut v___y_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
    mut v___y_2902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    v___x_2904_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(v_cls_2892_, v_msg_2893_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
    return v___x_2904_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(
    mut v_cls_2905_: *mut LeanObject,
    mut v_msg_2906_: *mut LeanObject,
    mut v___y_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
    mut v___y_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2917_: *mut LeanObject = core::ptr::null_mut();
    v_res_2917_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(v_cls_2905_, v_msg_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
    lean_dec(v___y_2915_);
    lean_dec_ref(v___y_2914_);
    lean_dec(v___y_2913_);
    lean_dec_ref(v___y_2912_);
    lean_dec(v___y_2911_);
    lean_dec_ref(v___y_2910_);
    lean_dec(v___y_2909_);
    lean_dec_ref(v___y_2908_);
    lean_dec(v___y_2907_);
    return v_res_2917_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(
    mut v_00_u03b2_2918_: *mut LeanObject,
    mut v_x_2919_: *mut LeanObject,
    mut v_x_2920_: usize,
    mut v_x_2921_: usize,
    mut v_x_2922_: *mut LeanObject,
    mut v_x_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(v_x_2919_, v_x_2920_, v_x_2921_, v_x_2922_, v_x_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(
    mut v_00_u03b2_2925_: *mut LeanObject,
    mut v_x_2926_: *mut LeanObject,
    mut v_x_2927_: *mut LeanObject,
    mut v_x_2928_: *mut LeanObject,
    mut v_x_2929_: *mut LeanObject,
    mut v_x_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_115851__boxed_2931_: usize = 0;
    let mut v_x_115852__boxed_2932_: usize = 0;
    let mut v_res_2933_: *mut LeanObject = core::ptr::null_mut();
    v_x_115851__boxed_2931_ = lean_unbox_usize(v_x_2927_);
    lean_dec(v_x_2927_);
    v_x_115852__boxed_2932_ = lean_unbox_usize(v_x_2928_);
    lean_dec(v_x_2928_);
    v_res_2933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(v_00_u03b2_2925_, v_x_2926_, v_x_115851__boxed_2931_, v_x_115852__boxed_2932_, v_x_2929_, v_x_2930_);
    return v_res_2933_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(
    mut v_00_u03b2_2934_: *mut LeanObject,
    mut v_x_2935_: *mut LeanObject,
    mut v_x_2936_: usize,
    mut v_x_2937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    v___x_2938_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(v_x_2935_, v_x_2936_, v_x_2937_);
    return v___x_2938_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(
    mut v_00_u03b2_2939_: *mut LeanObject,
    mut v_x_2940_: *mut LeanObject,
    mut v_x_2941_: *mut LeanObject,
    mut v_x_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_115868__boxed_2943_: usize = 0;
    let mut v_res_2944_: *mut LeanObject = core::ptr::null_mut();
    v_x_115868__boxed_2943_ = lean_unbox_usize(v_x_2941_);
    lean_dec(v_x_2941_);
    v_res_2944_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(v_00_u03b2_2939_, v_x_2940_, v_x_115868__boxed_2943_, v_x_2942_);
    lean_dec_ref(v_x_2942_);
    lean_dec_ref(v_x_2940_);
    return v_res_2944_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2945_: *mut LeanObject,
    mut v_n_2946_: *mut LeanObject,
    mut v_k_2947_: *mut LeanObject,
    mut v_v_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(v_n_2946_, v_k_2947_, v_v_2948_);
    return v___x_2949_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(
    mut v_00_u03b2_2950_: *mut LeanObject,
    mut v_depth_2951_: usize,
    mut v_keys_2952_: *mut LeanObject,
    mut v_vals_2953_: *mut LeanObject,
    mut v_heq_2954_: *mut LeanObject,
    mut v_i_2955_: *mut LeanObject,
    mut v_entries_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    v___x_2957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(v_depth_2951_, v_keys_2952_, v_vals_2953_, v_i_2955_, v_entries_2956_);
    return v___x_2957_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_2958_: *mut LeanObject,
    mut v_depth_2959_: *mut LeanObject,
    mut v_keys_2960_: *mut LeanObject,
    mut v_vals_2961_: *mut LeanObject,
    mut v_heq_2962_: *mut LeanObject,
    mut v_i_2963_: *mut LeanObject,
    mut v_entries_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2965_: usize = 0;
    let mut v_res_2966_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2965_ = lean_unbox_usize(v_depth_2959_);
    lean_dec(v_depth_2959_);
    v_res_2966_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(v_00_u03b2_2958_, v_depth_boxed_2965_, v_keys_2960_, v_vals_2961_, v_heq_2962_, v_i_2963_, v_entries_2964_);
    lean_dec_ref(v_vals_2961_);
    lean_dec_ref(v_keys_2960_);
    return v_res_2966_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(
    mut v_00_u03b2_2967_: *mut LeanObject,
    mut v_keys_2968_: *mut LeanObject,
    mut v_vals_2969_: *mut LeanObject,
    mut v_heq_2970_: *mut LeanObject,
    mut v_i_2971_: *mut LeanObject,
    mut v_k_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(v_keys_2968_, v_vals_2969_, v_i_2971_, v_k_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_2974_: *mut LeanObject,
    mut v_keys_2975_: *mut LeanObject,
    mut v_vals_2976_: *mut LeanObject,
    mut v_heq_2977_: *mut LeanObject,
    mut v_i_2978_: *mut LeanObject,
    mut v_k_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2980_: *mut LeanObject = core::ptr::null_mut();
    v_res_2980_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(v_00_u03b2_2974_, v_keys_2975_, v_vals_2976_, v_heq_2977_, v_i_2978_, v_k_2979_);
    lean_dec_ref(v_k_2979_);
    lean_dec_ref(v_vals_2976_);
    lean_dec_ref(v_keys_2975_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_2981_: *mut LeanObject,
    mut v_x_2982_: *mut LeanObject,
    mut v_x_2983_: *mut LeanObject,
    mut v_x_2984_: *mut LeanObject,
    mut v_x_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    v___x_2986_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__5___redArg(v_x_2982_, v_x_2983_, v_x_2984_, v_x_2985_);
    return v___x_2986_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Main_2936340881____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Main(builtin);
}
