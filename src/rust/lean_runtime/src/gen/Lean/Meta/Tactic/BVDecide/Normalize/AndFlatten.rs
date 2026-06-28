// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten
// Imports: Std.Tactic.BVDecide.Normalize.Bool Lean.Meta.Tactic.BVDecide.Normalize.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr6};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hash,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_instBEqFVarId_beq,
    l_Lean_instHashableFVarId_hash, l_Lean_mkApp3, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_userName;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_FVarId_getType___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assertHypotheses;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClearMany;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps;
use crate::r#gen::Std::Tactic::BVDecide::Normalize::Bool::{
    initialize_Std_Tactic_BVDecide_Normalize_Bool,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool,
};
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8_value) as *mut LeanObject,9255189395584251158 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0_value) as *mut LeanObject,6148012076188572320 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [78, 111, 114, 109, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 110, 100, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value) as *mut LeanObject,1678646150249543785 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value) as *mut LeanObject,6288000380003861824 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6_value) as *mut LeanObject,15487863038110484607 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 100, 95, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value) as *mut LeanObject,1678646150249543785 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value) as *mut LeanObject,6288000380003861824 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9_value) as *mut LeanObject,4528438387461145536 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1_value:
    LeanStringObject<14> = LeanStringObject {
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
        97, 110, 100, 70, 108, 97, 116, 116, 101, 110, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1_value
        ) as *mut LeanObject,
        4151274584932640964 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3_value)
        as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = lean_unsigned_to_nat(1);
    v___x_1122_ = l_Lean_Level_ofNat(v___x_1121_);
    return v___x_1122_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = lean_box(0);
    v___x_1124_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2);
    v___x_1125_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1125_, 0, v___x_1124_);
    lean_ctor_set(v___x_1125_, 1, v___x_1123_);
    return v___x_1125_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3);
    v___x_1127_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1;
    v___x_1128_ = l_Lean_mkConst(v___x_1127_, v___x_1126_);
    return v___x_1128_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = lean_box(0);
    v___x_1133_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6;
    v___x_1134_ = l_Lean_mkConst(v___x_1133_, v___x_1132_);
    return v___x_1134_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10()
-> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    v___x_1139_ = lean_box(0);
    v___x_1140_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9;
    v___x_1141_ = l_Lean_mkConst(v___x_1140_, v___x_1139_);
    return v___x_1141_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(
    mut v_lhs_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4);
    v___x_1144_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7);
    v___x_1145_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10);
    v___x_1146_ = l_Lean_mkApp3(v___x_1143_, v___x_1144_, v_lhs_1142_, v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(
    mut v_a_1147_: *mut LeanObject,
    mut v_x_1148_: *mut LeanObject,
) -> u8 {
    let mut v___x_1149_: u8 = 0;
    let mut v_key_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1148_) == 0 {
                    v___x_1149_ = 0;
                    return v___x_1149_;
                } else {
                    v_key_1150_ = lean_ctor_get(v_x_1148_, 0);
                    v_tail_1151_ = lean_ctor_get(v_x_1148_, 2);
                    v___x_1152_ = lean_expr_eqv(v_key_1150_, v_a_1147_);
                    if v___x_1152_ == 0 {
                        v_x_1148_ = v_tail_1151_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1152_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg___boxed(
    mut v_a_1154_: *mut LeanObject,
    mut v_x_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1156_: u8 = 0;
    let mut v_r_1157_: *mut LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_1154_, v_x_1155_);
    lean_dec(v_x_1155_);
    lean_dec_ref(v_a_1154_);
    v_r_1157_ = lean_box((v_res_1156_) as usize);
    return v_r_1157_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(
    mut v_m_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: u64 = 0;
    let mut v___x_1163_: u64 = 0;
    let mut v___x_1164_: u64 = 0;
    let mut v_fold_1165_: u64 = 0;
    let mut v___x_1166_: u64 = 0;
    let mut v___x_1167_: u64 = 0;
    let mut v___x_1168_: u64 = 0;
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: usize = 0;
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: usize = 0;
    let mut v___x_1173_: usize = 0;
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    v_buckets_1160_ = lean_ctor_get(v_m_1158_, 1);
    v___x_1161_ = lean_array_get_size(v_buckets_1160_);
    v___x_1162_ = l_Lean_Expr_hash(v_a_1159_);
    v___x_1163_ = 32u64;
    v___x_1164_ = lean_uint64_shift_right(v___x_1162_, v___x_1163_);
    v_fold_1165_ = lean_uint64_xor(v___x_1162_, v___x_1164_);
    v___x_1166_ = 16u64;
    v___x_1167_ = lean_uint64_shift_right(v_fold_1165_, v___x_1166_);
    v___x_1168_ = lean_uint64_xor(v_fold_1165_, v___x_1167_);
    v___x_1169_ = lean_uint64_to_usize(v___x_1168_);
    v___x_1170_ = lean_usize_of_nat(v___x_1161_);
    v___x_1171_ = 1usize;
    v___x_1172_ = lean_usize_sub(v___x_1170_, v___x_1171_);
    v___x_1173_ = lean_usize_land(v___x_1169_, v___x_1172_);
    v___x_1174_ = lean_array_uget_borrowed(v_buckets_1160_, v___x_1173_);
    v___x_1175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_1159_, v___x_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg___boxed(
    mut v_m_1176_: *mut LeanObject,
    mut v_a_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1178_: u8 = 0;
    let mut v_r_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_1176_, v_a_1177_);
    lean_dec_ref(v_a_1177_);
    lean_dec_ref(v_m_1176_);
    v_r_1179_ = lean_box((v_res_1178_) as usize);
    return v_r_1179_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_1180_: *mut LeanObject,
    mut v_x_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1187_: u8 = 0;
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u64 = 0;
    let mut v___x_1190_: u64 = 0;
    let mut v___x_1191_: u64 = 0;
    let mut v_fold_1192_: u64 = 0;
    let mut v___x_1193_: u64 = 0;
    let mut v___x_1194_: u64 = 0;
    let mut v___x_1195_: u64 = 0;
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v___x_1200_: usize = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1181_) == 0 {
                    return v_x_1180_;
                } else {
                    v_key_1182_ = lean_ctor_get(v_x_1181_, 0);
                    v_value_1183_ = lean_ctor_get(v_x_1181_, 1);
                    v_tail_1184_ = lean_ctor_get(v_x_1181_, 2);
                    v_isSharedCheck_1207_ = (!lean_is_exclusive(v_x_1181_)) as u8;
                    if v_isSharedCheck_1207_ == 0 {
                        v___x_1186_ = v_x_1181_;
                        v_isShared_1187_ = v_isSharedCheck_1207_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1184_);
                        lean_inc(v_value_1183_);
                        lean_inc(v_key_1182_);
                        lean_dec(v_x_1181_);
                        v___x_1186_ = lean_box(0);
                        v_isShared_1187_ = v_isSharedCheck_1207_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1188_ = lean_array_get_size(v_x_1180_);
                v___x_1189_ = l_Lean_Expr_hash(v_key_1182_);
                v___x_1190_ = 32u64;
                v___x_1191_ = lean_uint64_shift_right(v___x_1189_, v___x_1190_);
                v_fold_1192_ = lean_uint64_xor(v___x_1189_, v___x_1191_);
                v___x_1193_ = 16u64;
                v___x_1194_ = lean_uint64_shift_right(v_fold_1192_, v___x_1193_);
                v___x_1195_ = lean_uint64_xor(v_fold_1192_, v___x_1194_);
                v___x_1196_ = lean_uint64_to_usize(v___x_1195_);
                v___x_1197_ = lean_usize_of_nat(v___x_1188_);
                v___x_1198_ = 1usize;
                v___x_1199_ = lean_usize_sub(v___x_1197_, v___x_1198_);
                v___x_1200_ = lean_usize_land(v___x_1196_, v___x_1199_);
                v___x_1201_ = lean_array_uget_borrowed(v_x_1180_, v___x_1200_);
                lean_inc(v___x_1201_);
                if v_isShared_1187_ == 0 {
                    lean_ctor_set(v___x_1186_, 2, v___x_1201_);
                    v___x_1203_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_key_1182_);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_value_1183_);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 2, v___x_1201_);
                    v___x_1203_ = v_reuseFailAlloc_1206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1204_ = lean_array_uset(v_x_1180_, v___x_1200_, v___x_1203_);
                v_x_1180_ = v___x_1204_;
                v_x_1181_ = v_tail_1184_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(
    mut v_i_1208_: *mut LeanObject,
    mut v_source_1209_: *mut LeanObject,
    mut v_target_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v_es_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1211_ = lean_array_get_size(v_source_1209_);
                v___x_1212_ = lean_nat_dec_lt(v_i_1208_, v___x_1211_);
                if v___x_1212_ == 0 {
                    lean_dec_ref(v_source_1209_);
                    lean_dec(v_i_1208_);
                    return v_target_1210_;
                } else {
                    v_es_1213_ = lean_array_fget(v_source_1209_, v_i_1208_);
                    v___x_1214_ = lean_box(0);
                    v_source_1215_ = lean_array_fset(v_source_1209_, v_i_1208_, v___x_1214_);
                    v_target_1216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1210_, v_es_1213_);
                    v___x_1217_ = lean_unsigned_to_nat(1);
                    v___x_1218_ = lean_nat_add(v_i_1208_, v___x_1217_);
                    lean_dec(v_i_1208_);
                    v_i_1208_ = v___x_1218_;
                    v_source_1209_ = v_source_1215_;
                    v_target_1210_ = v_target_1216_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(
    mut v_data_1220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = lean_array_get_size(v_data_1220_);
    v___x_1222_ = lean_unsigned_to_nat(2);
    v_nbuckets_1223_ = lean_nat_mul(v___x_1221_, v___x_1222_);
    v___x_1224_ = lean_unsigned_to_nat(0);
    v___x_1225_ = lean_box(0);
    v___x_1226_ = lean_mk_array(v_nbuckets_1223_, v___x_1225_);
    v___x_1227_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v___x_1224_, v_data_1220_, v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(
    mut v_m_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
    mut v_b_1230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: u64 = 0;
    let mut v___x_1235_: u64 = 0;
    let mut v___x_1236_: u64 = 0;
    let mut v_fold_1237_: u64 = 0;
    let mut v___x_1238_: u64 = 0;
    let mut v___x_1239_: u64 = 0;
    let mut v___x_1240_: u64 = 0;
    let mut v___x_1241_: usize = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v_bkt_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v_val_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1268_: u8 = 0;
    let mut v_unused_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1231_ = lean_ctor_get(v_m_1228_, 0);
                v_buckets_1232_ = lean_ctor_get(v_m_1228_, 1);
                v___x_1233_ = lean_array_get_size(v_buckets_1232_);
                v___x_1234_ = l_Lean_Expr_hash(v_a_1229_);
                v___x_1235_ = 32u64;
                v___x_1236_ = lean_uint64_shift_right(v___x_1234_, v___x_1235_);
                v_fold_1237_ = lean_uint64_xor(v___x_1234_, v___x_1236_);
                v___x_1238_ = 16u64;
                v___x_1239_ = lean_uint64_shift_right(v_fold_1237_, v___x_1238_);
                v___x_1240_ = lean_uint64_xor(v_fold_1237_, v___x_1239_);
                v___x_1241_ = lean_uint64_to_usize(v___x_1240_);
                v___x_1242_ = lean_usize_of_nat(v___x_1233_);
                v___x_1243_ = 1usize;
                v___x_1244_ = lean_usize_sub(v___x_1242_, v___x_1243_);
                v___x_1245_ = lean_usize_land(v___x_1241_, v___x_1244_);
                v_bkt_1246_ = lean_array_uget_borrowed(v_buckets_1232_, v___x_1245_);
                v___x_1247_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_1229_, v_bkt_1246_);
                if v___x_1247_ == 0 {
                    lean_inc_ref(v_buckets_1232_);
                    lean_inc(v_size_1231_);
                    v_isSharedCheck_1268_ = (!lean_is_exclusive(v_m_1228_)) as u8;
                    if v_isSharedCheck_1268_ == 0 {
                        v_unused_1269_ = lean_ctor_get(v_m_1228_, 1);
                        lean_dec(v_unused_1269_);
                        v_unused_1270_ = lean_ctor_get(v_m_1228_, 0);
                        lean_dec(v_unused_1270_);
                        v___x_1249_ = v_m_1228_;
                        v_isShared_1250_ = v_isSharedCheck_1268_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1228_);
                        v___x_1249_ = lean_box(0);
                        v_isShared_1250_ = v_isSharedCheck_1268_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1230_);
                    lean_dec_ref(v_a_1229_);
                    return v_m_1228_;
                }
            }
            1 => {
                v___x_1251_ = lean_unsigned_to_nat(1);
                v_size_x27_1252_ = lean_nat_add(v_size_1231_, v___x_1251_);
                lean_dec(v_size_1231_);
                lean_inc(v_bkt_1246_);
                v___x_1253_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1253_, 0, v_a_1229_);
                lean_ctor_set(v___x_1253_, 1, v_b_1230_);
                lean_ctor_set(v___x_1253_, 2, v_bkt_1246_);
                v_buckets_x27_1254_ = lean_array_uset(v_buckets_1232_, v___x_1245_, v___x_1253_);
                v___x_1255_ = lean_unsigned_to_nat(4);
                v___x_1256_ = lean_nat_mul(v_size_x27_1252_, v___x_1255_);
                v___x_1257_ = lean_unsigned_to_nat(3);
                v___x_1258_ = lean_nat_div(v___x_1256_, v___x_1257_);
                lean_dec(v___x_1256_);
                v___x_1259_ = lean_array_get_size(v_buckets_x27_1254_);
                v___x_1260_ = lean_nat_dec_le(v___x_1258_, v___x_1259_);
                lean_dec(v___x_1258_);
                if v___x_1260_ == 0 {
                    v_val_1261_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_buckets_x27_1254_);
                    if v_isShared_1250_ == 0 {
                        lean_ctor_set(v___x_1249_, 1, v_val_1261_);
                        lean_ctor_set(v___x_1249_, 0, v_size_x27_1252_);
                        v___x_1263_ = v___x_1249_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_size_x27_1252_);
                        lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_val_1261_);
                        v___x_1263_ = v_reuseFailAlloc_1264_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1250_ == 0 {
                        lean_ctor_set(v___x_1249_, 1, v_buckets_x27_1254_);
                        lean_ctor_set(v___x_1249_, 0, v_size_x27_1252_);
                        v___x_1266_ = v___x_1249_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_size_x27_1252_);
                        lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_buckets_x27_1254_);
                        v___x_1266_ = v_reuseFailAlloc_1267_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1263_;
            }
            3 => {
                return v___x_1266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1287_ = lean_box(0);
    v___x_1288_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7;
    v___x_1289_ = l_Lean_mkConst(v___x_1288_, v___x_1287_);
    return v___x_1289_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = lean_box(0);
    v___x_1299_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10;
    v___x_1300_ = l_Lean_mkConst(v___x_1299_, v___x_1298_);
    return v___x_1300_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(
    mut v_hyp_1301_: *mut LeanObject,
    mut v_a_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyp_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_original_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v_userName_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v_cache_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToDelete_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToAdd_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v_arg_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v_arg_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: u8 = 0;
    let mut v_arg_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v_arg_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut v_isSharedCheck_1385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1307_ = lean_st_ref_get(v_a_1302_);
                v_hyp_1308_ = lean_ctor_get(v_hyp_1301_, 0);
                v_original_1309_ = lean_ctor_get(v_hyp_1301_, 1);
                v_isSharedCheck_1385_ = (!lean_is_exclusive(v_hyp_1301_)) as u8;
                if v_isSharedCheck_1385_ == 0 {
                    v___x_1311_ = v_hyp_1301_;
                    v_isShared_1312_ = v_isSharedCheck_1385_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_original_1309_);
                    lean_inc(v_hyp_1308_);
                    lean_dec(v_hyp_1301_);
                    v___x_1311_ = lean_box(0);
                    v_isShared_1312_ = v_isSharedCheck_1385_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1305_ = lean_box(0);
                v___x_1306_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                return v___x_1306_;
            }
            2 => {
                v_userName_1313_ = lean_ctor_get(v_hyp_1308_, 0);
                v_type_1314_ = lean_ctor_get(v_hyp_1308_, 1);
                v_value_1315_ = lean_ctor_get(v_hyp_1308_, 2);
                v_isSharedCheck_1384_ = (!lean_is_exclusive(v_hyp_1308_)) as u8;
                if v_isSharedCheck_1384_ == 0 {
                    v___x_1317_ = v_hyp_1308_;
                    v_isShared_1318_ = v_isSharedCheck_1384_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_value_1315_);
                    lean_inc(v_type_1314_);
                    lean_inc(v_userName_1313_);
                    lean_dec(v_hyp_1308_);
                    v___x_1317_ = lean_box(0);
                    v_isShared_1318_ = v_isSharedCheck_1384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_cache_1319_ = lean_ctor_get(v___x_1307_, 2);
                lean_inc_ref(v_cache_1319_);
                lean_dec(v___x_1307_);
                v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_cache_1319_, v_type_1314_);
                lean_dec_ref(v_cache_1319_);
                if v___x_1320_ == 0 {
                    v___x_1321_ = lean_st_ref_take(v_a_1302_);
                    v_hypsToDelete_1322_ = lean_ctor_get(v___x_1321_, 0);
                    v_hypsToAdd_1323_ = lean_ctor_get(v___x_1321_, 1);
                    v_cache_1324_ = lean_ctor_get(v___x_1321_, 2);
                    v_isSharedCheck_1381_ = (!lean_is_exclusive(v___x_1321_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1326_ = v___x_1321_;
                        v_isShared_1327_ = v_isSharedCheck_1381_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_cache_1324_);
                        lean_inc(v_hypsToAdd_1323_);
                        lean_inc(v_hypsToDelete_1322_);
                        lean_dec(v___x_1321_);
                        v___x_1326_ = lean_box(0);
                        v_isShared_1327_ = v_isSharedCheck_1381_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1317_);
                    lean_dec_ref(v_value_1315_);
                    lean_dec_ref(v_type_1314_);
                    lean_dec(v_userName_1313_);
                    lean_del_object(v___x_1311_);
                    lean_dec(v_original_1309_);
                    v___x_1382_ = lean_box(0);
                    v___x_1383_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1383_, 0, v___x_1382_);
                    return v___x_1383_;
                }
            }
            4 => {
                v___x_1328_ = lean_box(0);
                lean_inc_ref(v_type_1314_);
                v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v_cache_1324_, v_type_1314_, v___x_1328_);
                if v_isShared_1327_ == 0 {
                    lean_ctor_set(v___x_1326_, 2, v___x_1329_);
                    v___x_1331_ = v___x_1326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_hypsToDelete_1322_);
                    lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_hypsToAdd_1323_);
                    lean_ctor_set(v_reuseFailAlloc_1380_, 2, v___x_1329_);
                    v___x_1331_ = v_reuseFailAlloc_1380_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1332_ = lean_st_ref_set(v_a_1302_, v___x_1331_);
                v___x_1336_ = l_Lean_Expr_cleanupAnnotations(v_type_1314_);
                v___x_1337_ = l_Lean_Expr_isApp(v___x_1336_);
                if v___x_1337_ == 0 {
                    lean_dec_ref(v___x_1336_);
                    lean_del_object(v___x_1317_);
                    lean_dec_ref(v_value_1315_);
                    lean_dec(v_userName_1313_);
                    lean_del_object(v___x_1311_);
                    lean_dec(v_original_1309_);
                    state = 6;
                    continue;
                } else {
                    v_arg_1338_ = lean_ctor_get(v___x_1336_, 1);
                    lean_inc_ref(v_arg_1338_);
                    v___x_1339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1336_);
                    v___x_1340_ = l_Lean_Expr_isApp(v___x_1339_);
                    if v___x_1340_ == 0 {
                        lean_dec_ref(v___x_1339_);
                        lean_dec_ref(v_arg_1338_);
                        lean_del_object(v___x_1317_);
                        lean_dec_ref(v_value_1315_);
                        lean_dec(v_userName_1313_);
                        lean_del_object(v___x_1311_);
                        lean_dec(v_original_1309_);
                        state = 6;
                        continue;
                    } else {
                        v_arg_1341_ = lean_ctor_get(v___x_1339_, 1);
                        lean_inc_ref(v_arg_1341_);
                        v___x_1342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1339_);
                        v___x_1343_ = l_Lean_Expr_isApp(v___x_1342_);
                        if v___x_1343_ == 0 {
                            lean_dec_ref(v___x_1342_);
                            lean_dec_ref(v_arg_1341_);
                            lean_dec_ref(v_arg_1338_);
                            lean_del_object(v___x_1317_);
                            lean_dec_ref(v_value_1315_);
                            lean_dec(v_userName_1313_);
                            lean_del_object(v___x_1311_);
                            lean_dec(v_original_1309_);
                            state = 6;
                            continue;
                        } else {
                            v___x_1344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1342_);
                            v___x_1345_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1;
                            v___x_1346_ = l_Lean_Expr_isConstOf(v___x_1344_, v___x_1345_);
                            lean_dec_ref(v___x_1344_);
                            if v___x_1346_ == 0 {
                                lean_dec_ref(v_arg_1341_);
                                lean_dec_ref(v_arg_1338_);
                                lean_del_object(v___x_1317_);
                                lean_dec_ref(v_value_1315_);
                                lean_dec(v_userName_1313_);
                                lean_del_object(v___x_1311_);
                                lean_dec(v_original_1309_);
                                state = 6;
                                continue;
                            } else {
                                v___x_1347_ = l_Lean_Expr_cleanupAnnotations(v_arg_1341_);
                                v___x_1348_ = l_Lean_Expr_isApp(v___x_1347_);
                                if v___x_1348_ == 0 {
                                    lean_dec_ref(v___x_1347_);
                                    lean_dec_ref(v_arg_1338_);
                                    lean_del_object(v___x_1317_);
                                    lean_dec_ref(v_value_1315_);
                                    lean_dec(v_userName_1313_);
                                    lean_del_object(v___x_1311_);
                                    lean_dec(v_original_1309_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_1349_ = lean_ctor_get(v___x_1347_, 1);
                                    lean_inc_ref(v_arg_1349_);
                                    v___x_1350_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1347_);
                                    v___x_1351_ = l_Lean_Expr_isApp(v___x_1350_);
                                    if v___x_1351_ == 0 {
                                        lean_dec_ref(v___x_1350_);
                                        lean_dec_ref(v_arg_1349_);
                                        lean_dec_ref(v_arg_1338_);
                                        lean_del_object(v___x_1317_);
                                        lean_dec_ref(v_value_1315_);
                                        lean_dec(v_userName_1313_);
                                        lean_del_object(v___x_1311_);
                                        lean_dec(v_original_1309_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_1352_ = lean_ctor_get(v___x_1350_, 1);
                                        lean_inc_ref(v_arg_1352_);
                                        v___x_1353_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1350_);
                                        v___x_1354_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1;
                                        v___x_1355_ =
                                            l_Lean_Expr_isConstOf(v___x_1353_, v___x_1354_);
                                        lean_dec_ref(v___x_1353_);
                                        if v___x_1355_ == 0 {
                                            lean_dec_ref(v_arg_1352_);
                                            lean_dec_ref(v_arg_1349_);
                                            lean_dec_ref(v_arg_1338_);
                                            lean_del_object(v___x_1317_);
                                            lean_dec_ref(v_value_1315_);
                                            lean_dec(v_userName_1313_);
                                            lean_del_object(v___x_1311_);
                                            lean_dec(v_original_1309_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_1356_ =
                                                l_Lean_Expr_cleanupAnnotations(v_arg_1338_);
                                            v___x_1357_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9;
                                            v___x_1358_ =
                                                l_Lean_Expr_isConstOf(v___x_1356_, v___x_1357_);
                                            lean_dec_ref(v___x_1356_);
                                            if v___x_1358_ == 0 {
                                                lean_dec_ref(v_arg_1352_);
                                                lean_dec_ref(v_arg_1349_);
                                                lean_del_object(v___x_1317_);
                                                lean_dec_ref(v_value_1315_);
                                                lean_dec(v_userName_1313_);
                                                lean_del_object(v___x_1311_);
                                                lean_dec(v_original_1309_);
                                                v___x_1359_ = lean_box(0);
                                                v___x_1360_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v___x_1360_, 0, v___x_1359_);
                                                return v___x_1360_;
                                            } else {
                                                lean_inc_ref_n(v_arg_1352_, 2);
                                                v___x_1361_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_1352_);
                                                v___x_1362_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8);
                                                lean_inc_ref(v_value_1315_);
                                                lean_inc_ref(v_arg_1349_);
                                                v___x_1363_ = l_Lean_mkApp3(
                                                    v___x_1362_,
                                                    v_arg_1352_,
                                                    v_arg_1349_,
                                                    v_value_1315_,
                                                );
                                                v___x_1364_ = 0;
                                                v___x_1365_ = 0;
                                                lean_inc(v_userName_1313_);
                                                if v_isShared_1318_ == 0 {
                                                    lean_ctor_set(v___x_1317_, 2, v___x_1363_);
                                                    lean_ctor_set(v___x_1317_, 1, v___x_1361_);
                                                    v___x_1367_ = v___x_1317_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_1379_ =
                                                        lean_alloc_ctor(0, 3, (2) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_1379_,
                                                        0,
                                                        v_userName_1313_,
                                                    );
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_1379_,
                                                        1,
                                                        v___x_1361_,
                                                    );
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_1379_,
                                                        2,
                                                        v___x_1363_,
                                                    );
                                                    v___x_1367_ = v_reuseFailAlloc_1379_;
                                                    state = 7;
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
            6 => {
                v___x_1334_ = lean_box(0);
                v___x_1335_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1335_, 0, v___x_1334_);
                return v___x_1335_;
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_1367_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1364_,
                );
                lean_ctor_set_uint8(
                    v___x_1367_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_1365_,
                );
                lean_inc_ref(v_arg_1349_);
                v___x_1368_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_1349_);
                v___x_1369_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11);
                v___x_1370_ = l_Lean_mkApp3(v___x_1369_, v_arg_1352_, v_arg_1349_, v_value_1315_);
                v___x_1371_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_1371_, 0, v_userName_1313_);
                lean_ctor_set(v___x_1371_, 1, v___x_1368_);
                lean_ctor_set(v___x_1371_, 2, v___x_1370_);
                lean_ctor_set_uint8(
                    v___x_1371_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1364_,
                );
                lean_ctor_set_uint8(
                    v___x_1371_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_1365_,
                );
                lean_inc(v_original_1309_);
                if v_isShared_1312_ == 0 {
                    lean_ctor_set(v___x_1311_, 0, v___x_1367_);
                    v___x_1373_ = v___x_1311_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1367_);
                    lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_original_1309_);
                    v___x_1373_ = v_reuseFailAlloc_1378_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1374_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1374_, 0, v___x_1371_);
                lean_ctor_set(v___x_1374_, 1, v_original_1309_);
                v___x_1375_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1375_, 0, v___x_1373_);
                lean_ctor_set(v___x_1375_, 1, v___x_1374_);
                v___x_1376_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1376_, 0, v___x_1375_);
                v___x_1377_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1377_, 0, v___x_1376_);
                return v___x_1377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___boxed(
    mut v_hyp_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1389_: *mut LeanObject = core::ptr::null_mut();
    v_res_1389_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_1386_, v_a_1387_);
    lean_dec(v_a_1387_);
    return v_res_1389_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(
    mut v_hyp_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    v___x_1397_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_1390_, v_a_1391_);
    return v___x_1397_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___boxed(
    mut v_hyp_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1405_: *mut LeanObject = core::ptr::null_mut();
    v_res_1405_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(v_hyp_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
    lean_dec(v_a_1403_);
    lean_dec_ref(v_a_1402_);
    lean_dec(v_a_1401_);
    lean_dec_ref(v_a_1400_);
    lean_dec(v_a_1399_);
    return v_res_1405_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(
    mut v_00_u03b2_1406_: *mut LeanObject,
    mut v_m_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
) -> u8 {
    let mut v___x_1409_: u8 = 0;
    v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_1407_, v_a_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___boxed(
    mut v_00_u03b2_1410_: *mut LeanObject,
    mut v_m_1411_: *mut LeanObject,
    mut v_a_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1413_: u8 = 0;
    let mut v_r_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(v_00_u03b2_1410_, v_m_1411_, v_a_1412_);
    lean_dec_ref(v_a_1412_);
    lean_dec_ref(v_m_1411_);
    v_r_1414_ = lean_box((v_res_1413_) as usize);
    return v_r_1414_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1(
    mut v_00_u03b2_1415_: *mut LeanObject,
    mut v_m_1416_: *mut LeanObject,
    mut v_a_1417_: *mut LeanObject,
    mut v_b_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v_m_1416_, v_a_1417_, v_b_1418_);
    return v___x_1419_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(
    mut v_00_u03b2_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
    mut v_x_1422_: *mut LeanObject,
) -> u8 {
    let mut v___x_1423_: u8 = 0;
    v___x_1423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_1421_, v_x_1422_);
    return v___x_1423_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___boxed(
    mut v_00_u03b2_1424_: *mut LeanObject,
    mut v_a_1425_: *mut LeanObject,
    mut v_x_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1427_: u8 = 0;
    let mut v_r_1428_: *mut LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(v_00_u03b2_1424_, v_a_1425_, v_x_1426_);
    lean_dec(v_x_1426_);
    lean_dec_ref(v_a_1425_);
    v_r_1428_ = lean_box((v_res_1427_) as usize);
    return v_r_1428_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2(
    mut v_00_u03b2_1429_: *mut LeanObject,
    mut v_data_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_data_1430_);
    return v___x_1431_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1432_: *mut LeanObject,
    mut v_i_1433_: *mut LeanObject,
    mut v_source_1434_: *mut LeanObject,
    mut v_target_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1436_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v_i_1433_, v_source_1434_, v_target_1435_);
    return v___x_1436_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1437_: *mut LeanObject,
    mut v_x_1438_: *mut LeanObject,
    mut v_x_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1438_, v_x_1439_);
    return v___x_1440_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(
    mut v_worklist_1441_: *mut LeanObject,
    mut v_a_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToDelete_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToAdd_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut v_val_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut v_a_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_worklist_1441_) == 0 {
                    v___x_1444_ = lean_box(0);
                    v___x_1445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1445_, 0, v___x_1444_);
                    return v___x_1445_;
                } else {
                    v_head_1446_ = lean_ctor_get(v_worklist_1441_, 0);
                    v_tail_1447_ = lean_ctor_get(v_worklist_1441_, 1);
                    v_isSharedCheck_1489_ = (!lean_is_exclusive(v_worklist_1441_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1449_ = v_worklist_1441_;
                        v_isShared_1450_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1447_);
                        lean_inc(v_head_1446_);
                        lean_dec(v_worklist_1441_);
                        v___x_1449_ = lean_box(0);
                        v_isShared_1450_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_1446_);
                v___x_1451_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_head_1446_, v_a_1442_);
                if lean_obj_tag(v___x_1451_) == 0 {
                    v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
                    lean_inc(v_a_1452_);
                    lean_dec_ref_known(v___x_1451_, 1);
                    if lean_obj_tag(v_a_1452_) == 0 {
                        lean_del_object(v___x_1449_);
                        v___x_1453_ = lean_st_ref_take(v_a_1442_);
                        v_hypsToDelete_1454_ = lean_ctor_get(v___x_1453_, 0);
                        v_hypsToAdd_1455_ = lean_ctor_get(v___x_1453_, 1);
                        v_cache_1456_ = lean_ctor_get(v___x_1453_, 2);
                        v_isSharedCheck_1466_ = (!lean_is_exclusive(v___x_1453_)) as u8;
                        if v_isSharedCheck_1466_ == 0 {
                            v___x_1458_ = v___x_1453_;
                            v_isShared_1459_ = v_isSharedCheck_1466_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_cache_1456_);
                            lean_inc(v_hypsToAdd_1455_);
                            lean_inc(v_hypsToDelete_1454_);
                            lean_dec(v___x_1453_);
                            v___x_1458_ = lean_box(0);
                            v_isShared_1459_ = v_isSharedCheck_1466_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_head_1446_);
                        v_val_1467_ = lean_ctor_get(v_a_1452_, 0);
                        lean_inc(v_val_1467_);
                        lean_dec_ref_known(v_a_1452_, 1);
                        v_fst_1468_ = lean_ctor_get(v_val_1467_, 0);
                        v_snd_1469_ = lean_ctor_get(v_val_1467_, 1);
                        v_isSharedCheck_1480_ = (!lean_is_exclusive(v_val_1467_)) as u8;
                        if v_isSharedCheck_1480_ == 0 {
                            v___x_1471_ = v_val_1467_;
                            v_isShared_1472_ = v_isSharedCheck_1480_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_1469_);
                            lean_inc(v_fst_1468_);
                            lean_dec(v_val_1467_);
                            v___x_1471_ = lean_box(0);
                            v_isShared_1472_ = v_isSharedCheck_1480_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1449_);
                    lean_dec(v_tail_1447_);
                    lean_dec(v_head_1446_);
                    v_a_1481_ = lean_ctor_get(v___x_1451_, 0);
                    v_isSharedCheck_1488_ = (!lean_is_exclusive(v___x_1451_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1483_ = v___x_1451_;
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1481_);
                        lean_dec(v___x_1451_);
                        v___x_1483_ = lean_box(0);
                        v_isShared_1484_ = v_isSharedCheck_1488_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1460_ = lean_array_push(v_hypsToAdd_1455_, v_head_1446_);
                if v_isShared_1459_ == 0 {
                    lean_ctor_set(v___x_1458_, 1, v___x_1460_);
                    v___x_1462_ = v___x_1458_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_hypsToDelete_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1460_);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_cache_1456_);
                    v___x_1462_ = v_reuseFailAlloc_1465_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1463_ = lean_st_ref_set(v_a_1442_, v___x_1462_);
                v_worklist_1441_ = v_tail_1447_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_1450_ == 0 {
                    lean_ctor_set(v___x_1449_, 0, v_snd_1469_);
                    v___x_1474_ = v___x_1449_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_snd_1469_);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_tail_1447_);
                    v___x_1474_ = v_reuseFailAlloc_1479_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1472_ == 0 {
                    lean_ctor_set_tag(v___x_1471_, 1);
                    lean_ctor_set(v___x_1471_, 1, v___x_1474_);
                    v___x_1476_ = v___x_1471_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_fst_1468_);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1474_);
                    v___x_1476_ = v_reuseFailAlloc_1478_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_worklist_1441_ = v___x_1476_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_1484_ == 0 {
                    v___x_1486_ = v___x_1483_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
                    v___x_1486_ = v_reuseFailAlloc_1487_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg___boxed(
    mut v_worklist_1490_: *mut LeanObject,
    mut v_a_1491_: *mut LeanObject,
    mut v_a_1492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1493_: *mut LeanObject = core::ptr::null_mut();
    v_res_1493_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_1490_, v_a_1491_);
    lean_dec(v_a_1491_);
    return v_res_1493_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(
    mut v_fvar_1494_: *mut LeanObject,
    mut v_worklist_1495_: *mut LeanObject,
    mut v_a_1496_: *mut LeanObject,
    mut v_a_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_1495_, v_a_1496_);
    return v___x_1502_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___boxed(
    mut v_fvar_1503_: *mut LeanObject,
    mut v_worklist_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v_a_1509_: *mut LeanObject,
    mut v_a_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1511_: *mut LeanObject = core::ptr::null_mut();
    v_res_1511_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(v_fvar_1503_, v_worklist_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
    lean_dec(v_a_1509_);
    lean_dec_ref(v_a_1508_);
    lean_dec(v_a_1507_);
    lean_dec_ref(v_a_1506_);
    lean_dec(v_a_1505_);
    lean_dec(v_fvar_1503_);
    return v_res_1511_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar___redArg(
    mut v_fvar_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
    mut v_a_1515_: *mut LeanObject,
    mut v_a_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v_val_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToDelete_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToAdd_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v_isSharedCheck_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1569_: u8 = 0;
    let mut v_a_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1573_: u8 = 0;
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToDelete_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToAdd_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_a_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvar_1512_);
                v___x_1518_ =
                    l_Lean_FVarId_getType___redArg(v_fvar_1512_, v_a_1514_, v_a_1515_, v_a_1516_);
                if lean_obj_tag(v___x_1518_) == 0 {
                    v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
                    v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1518_)) as u8;
                    if v_isSharedCheck_1595_ == 0 {
                        v___x_1521_ = v___x_1518_;
                        v_isShared_1522_ = v_isSharedCheck_1595_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1519_);
                        lean_dec(v___x_1518_);
                        v___x_1521_ = lean_box(0);
                        v_isShared_1522_ = v_isSharedCheck_1595_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fvar_1512_);
                    v_a_1596_ = lean_ctor_get(v___x_1518_, 0);
                    v_isSharedCheck_1603_ = (!lean_is_exclusive(v___x_1518_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1598_ = v___x_1518_;
                        v_isShared_1599_ = v_isSharedCheck_1603_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_1596_);
                        lean_dec(v___x_1518_);
                        v___x_1598_ = lean_box(0);
                        v_isShared_1599_ = v_isSharedCheck_1603_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1523_ = lean_st_ref_get(v_a_1513_);
                v_cache_1524_ = lean_ctor_get(v___x_1523_, 2);
                lean_inc_ref(v_cache_1524_);
                lean_dec(v___x_1523_);
                v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_cache_1524_, v_a_1519_);
                lean_dec_ref(v_cache_1524_);
                if v___x_1525_ == 0 {
                    lean_del_object(v___x_1521_);
                    lean_inc(v_fvar_1512_);
                    v___x_1526_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvar_1512_,
                        v_a_1514_,
                        v_a_1515_,
                        v_a_1516_,
                    );
                    if lean_obj_tag(v___x_1526_) == 0 {
                        v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
                        lean_inc(v_a_1527_);
                        lean_dec_ref_known(v___x_1526_, 1);
                        v___x_1528_ = l_Lean_LocalDecl_userName(v_a_1527_);
                        lean_dec(v_a_1527_);
                        lean_inc_n(v_fvar_1512_, 2);
                        v___x_1529_ = l_Lean_mkFVar(v_fvar_1512_);
                        v___x_1530_ = 0;
                        v___x_1531_ = 0;
                        v___x_1532_ = lean_alloc_ctor(0, 3, (2) as u32);
                        lean_ctor_set(v___x_1532_, 0, v___x_1528_);
                        lean_ctor_set(v___x_1532_, 1, v_a_1519_);
                        lean_ctor_set(v___x_1532_, 2, v___x_1529_);
                        lean_ctor_set_uint8(
                            v___x_1532_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_1530_,
                        );
                        lean_ctor_set_uint8(
                            v___x_1532_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v___x_1531_,
                        );
                        v___x_1533_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                        lean_ctor_set(v___x_1533_, 1, v_fvar_1512_);
                        v___x_1534_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v___x_1533_, v_a_1513_);
                        v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
                        v_isSharedCheck_1569_ = (!lean_is_exclusive(v___x_1534_)) as u8;
                        if v_isSharedCheck_1569_ == 0 {
                            v___x_1537_ = v___x_1534_;
                            v_isShared_1538_ = v_isSharedCheck_1569_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1535_);
                            lean_dec(v___x_1534_);
                            v___x_1537_ = lean_box(0);
                            v_isShared_1538_ = v_isSharedCheck_1569_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1519_);
                        lean_dec(v_fvar_1512_);
                        v_a_1570_ = lean_ctor_get(v___x_1526_, 0);
                        v_isSharedCheck_1577_ = (!lean_is_exclusive(v___x_1526_)) as u8;
                        if v_isSharedCheck_1577_ == 0 {
                            v___x_1572_ = v___x_1526_;
                            v_isShared_1573_ = v_isSharedCheck_1577_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1570_);
                            lean_dec(v___x_1526_);
                            v___x_1572_ = lean_box(0);
                            v_isShared_1573_ = v_isSharedCheck_1577_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1519_);
                    v___x_1578_ = lean_st_ref_take(v_a_1513_);
                    v_hypsToDelete_1579_ = lean_ctor_get(v___x_1578_, 0);
                    v_hypsToAdd_1580_ = lean_ctor_get(v___x_1578_, 1);
                    v_cache_1581_ = lean_ctor_get(v___x_1578_, 2);
                    v_isSharedCheck_1594_ = (!lean_is_exclusive(v___x_1578_)) as u8;
                    if v_isSharedCheck_1594_ == 0 {
                        v___x_1583_ = v___x_1578_;
                        v_isShared_1584_ = v_isSharedCheck_1594_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_cache_1581_);
                        lean_inc(v_hypsToAdd_1580_);
                        lean_inc(v_hypsToDelete_1579_);
                        lean_dec(v___x_1578_);
                        v___x_1583_ = lean_box(0);
                        v_isShared_1584_ = v_isSharedCheck_1594_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1535_) == 1 {
                    lean_del_object(v___x_1537_);
                    v_val_1539_ = lean_ctor_get(v_a_1535_, 0);
                    lean_inc(v_val_1539_);
                    lean_dec_ref_known(v_a_1535_, 1);
                    v_fst_1540_ = lean_ctor_get(v_val_1539_, 0);
                    v_snd_1541_ = lean_ctor_get(v_val_1539_, 1);
                    v_isSharedCheck_1564_ = (!lean_is_exclusive(v_val_1539_)) as u8;
                    if v_isSharedCheck_1564_ == 0 {
                        v___x_1543_ = v_val_1539_;
                        v_isShared_1544_ = v_isSharedCheck_1564_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_1541_);
                        lean_inc(v_fst_1540_);
                        lean_dec(v_val_1539_);
                        v___x_1543_ = lean_box(0);
                        v_isShared_1544_ = v_isSharedCheck_1564_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1535_);
                    lean_dec(v_fvar_1512_);
                    v___x_1565_ = lean_box(0);
                    if v_isShared_1538_ == 0 {
                        lean_ctor_set(v___x_1537_, 0, v___x_1565_);
                        v___x_1567_ = v___x_1537_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                        v___x_1567_ = v_reuseFailAlloc_1568_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1545_ = lean_st_ref_take(v_a_1513_);
                v_hypsToDelete_1546_ = lean_ctor_get(v___x_1545_, 0);
                v_hypsToAdd_1547_ = lean_ctor_get(v___x_1545_, 1);
                v_cache_1548_ = lean_ctor_get(v___x_1545_, 2);
                v_isSharedCheck_1563_ = (!lean_is_exclusive(v___x_1545_)) as u8;
                if v_isSharedCheck_1563_ == 0 {
                    v___x_1550_ = v___x_1545_;
                    v_isShared_1551_ = v_isSharedCheck_1563_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_cache_1548_);
                    lean_inc(v_hypsToAdd_1547_);
                    lean_inc(v_hypsToDelete_1546_);
                    lean_dec(v___x_1545_);
                    v___x_1550_ = lean_box(0);
                    v_isShared_1551_ = v_isSharedCheck_1563_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1552_ = lean_array_push(v_hypsToDelete_1546_, v_fvar_1512_);
                if v_isShared_1551_ == 0 {
                    lean_ctor_set(v___x_1550_, 0, v___x_1552_);
                    v___x_1554_ = v___x_1550_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1552_);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_hypsToAdd_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_cache_1548_);
                    v___x_1554_ = v_reuseFailAlloc_1562_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1555_ = lean_st_ref_set(v_a_1513_, v___x_1554_);
                v___x_1556_ = lean_box(0);
                if v_isShared_1544_ == 0 {
                    lean_ctor_set_tag(v___x_1543_, 1);
                    lean_ctor_set(v___x_1543_, 1, v___x_1556_);
                    lean_ctor_set(v___x_1543_, 0, v_snd_1541_);
                    v___x_1558_ = v___x_1543_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_snd_1541_);
                    lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1556_);
                    v___x_1558_ = v_reuseFailAlloc_1561_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1559_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1559_, 0, v_fst_1540_);
                lean_ctor_set(v___x_1559_, 1, v___x_1558_);
                v___x_1560_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v___x_1559_, v_a_1513_);
                return v___x_1560_;
            }
            7 => {
                return v___x_1567_;
            }
            8 => {
                if v_isShared_1573_ == 0 {
                    v___x_1575_ = v___x_1572_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
                    v___x_1575_ = v_reuseFailAlloc_1576_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1575_;
            }
            10 => {
                v___x_1585_ = lean_array_push(v_hypsToDelete_1579_, v_fvar_1512_);
                if v_isShared_1584_ == 0 {
                    lean_ctor_set(v___x_1583_, 0, v___x_1585_);
                    v___x_1587_ = v___x_1583_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1585_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_hypsToAdd_1580_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_cache_1581_);
                    v___x_1587_ = v_reuseFailAlloc_1593_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1588_ = lean_st_ref_set(v_a_1513_, v___x_1587_);
                v___x_1589_ = lean_box(0);
                if v_isShared_1522_ == 0 {
                    lean_ctor_set(v___x_1521_, 0, v___x_1589_);
                    v___x_1591_ = v___x_1521_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
                    v___x_1591_ = v_reuseFailAlloc_1592_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1591_;
            }
            13 => {
                if v_isShared_1599_ == 0 {
                    v___x_1601_ = v___x_1598_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
                    v___x_1601_ = v_reuseFailAlloc_1602_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar___redArg___boxed(
    mut v_fvar_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1610_: *mut LeanObject = core::ptr::null_mut();
    v_res_1610_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar___redArg(v_fvar_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
    lean_dec(v_a_1608_);
    lean_dec_ref(v_a_1607_);
    lean_dec_ref(v_a_1606_);
    lean_dec(v_a_1605_);
    return v_res_1610_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar(
    mut v_fvar_1611_: *mut LeanObject,
    mut v_a_1612_: *mut LeanObject,
    mut v_a_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
    mut v_a_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar___redArg(v_fvar_1611_, v_a_1612_, v_a_1613_, v_a_1615_, v_a_1616_);
    return v___x_1618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar___boxed(
    mut v_fvar_1619_: *mut LeanObject,
    mut v_a_1620_: *mut LeanObject,
    mut v_a_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar(v_fvar_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
    lean_dec(v_a_1624_);
    lean_dec_ref(v_a_1623_);
    lean_dec(v_a_1622_);
    lean_dec_ref(v_a_1621_);
    lean_dec(v_a_1620_);
    return v_res_1626_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0(
    mut v_x_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1628_);
    v___x_1634_ = lean_apply_6(
        v_x_1627_,
        v___y_1628_,
        v___y_1629_,
        v___y_1630_,
        v___y_1631_,
        v___y_1632_,
        lean_box(0),
    );
    return v___x_1634_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0___boxed(
    mut v_x_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1642_: *mut LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0(v_x_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
    lean_dec(v___y_1636_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg(
    mut v_mvarId_1643_: *mut LeanObject,
    mut v_x_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1645_);
                v___f_1651_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                lean_closure_set(v___f_1651_, 0, v_x_1644_);
                lean_closure_set(v___f_1651_, 1, v___y_1645_);
                v___x_1652_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1643_,
                    v___f_1651_,
                    v___y_1646_,
                    v___y_1647_,
                    v___y_1648_,
                    v___y_1649_,
                );
                if lean_obj_tag(v___x_1652_) == 0 {
                    return v___x_1652_;
                } else {
                    v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
                    v_isSharedCheck_1660_ = (!lean_is_exclusive(v___x_1652_)) as u8;
                    if v_isSharedCheck_1660_ == 0 {
                        v___x_1655_ = v___x_1652_;
                        v_isShared_1656_ = v_isSharedCheck_1660_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1653_);
                        lean_dec(v___x_1652_);
                        v___x_1655_ = lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1660_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1656_ == 0 {
                    v___x_1658_ = v___x_1655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
                    v___x_1658_ = v_reuseFailAlloc_1659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg___boxed(
    mut v_mvarId_1661_: *mut LeanObject,
    mut v_x_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1669_: *mut LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg(v_mvarId_1661_, v_x_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
    lean_dec(v___y_1667_);
    lean_dec_ref(v___y_1666_);
    lean_dec(v___y_1665_);
    lean_dec_ref(v___y_1664_);
    lean_dec(v___y_1663_);
    return v_res_1669_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1(
    mut v_00_u03b1_1670_: *mut LeanObject,
    mut v_mvarId_1671_: *mut LeanObject,
    mut v_x_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    v___x_1679_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg(v_mvarId_1671_, v_x_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
    return v___x_1679_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___boxed(
    mut v_00_u03b1_1680_: *mut LeanObject,
    mut v_mvarId_1681_: *mut LeanObject,
    mut v_x_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1689_: *mut LeanObject = core::ptr::null_mut();
    v_res_1689_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1(v_00_u03b1_1680_, v_mvarId_1681_, v_x_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
    lean_dec(v___y_1687_);
    lean_dec_ref(v___y_1686_);
    lean_dec(v___y_1685_);
    lean_dec_ref(v___y_1684_);
    lean_dec(v___y_1683_);
    return v_res_1689_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___redArg(
    mut v_as_1690_: *mut LeanObject,
    mut v_i_1691_: usize,
    mut v_stop_1692_: usize,
    mut v_b_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1699_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: usize = 0;
    let mut v___x_1704_: usize = 0;
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1699_ = lean_usize_dec_eq(v_i_1691_, v_stop_1692_);
                if v___x_1699_ == 0 {
                    v___x_1700_ = lean_array_uget_borrowed(v_as_1690_, v_i_1691_);
                    lean_inc(v___x_1700_);
                    v___x_1701_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processFVar___redArg(v___x_1700_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
                    if lean_obj_tag(v___x_1701_) == 0 {
                        v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
                        lean_inc(v_a_1702_);
                        lean_dec_ref_known(v___x_1701_, 1);
                        v___x_1703_ = 1usize;
                        v___x_1704_ = lean_usize_add(v_i_1691_, v___x_1703_);
                        v_i_1691_ = v___x_1704_;
                        v_b_1693_ = v_a_1702_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1701_;
                    }
                } else {
                    v___x_1706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1706_, 0, v_b_1693_);
                    return v___x_1706_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___redArg___boxed(
    mut v_as_1707_: *mut LeanObject,
    mut v_i_1708_: *mut LeanObject,
    mut v_stop_1709_: *mut LeanObject,
    mut v_b_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1716_: usize = 0;
    let mut v_stop_boxed_1717_: usize = 0;
    let mut v_res_1718_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1716_ = lean_unbox_usize(v_i_1708_);
    lean_dec(v_i_1708_);
    v_stop_boxed_1717_ = lean_unbox_usize(v_stop_1709_);
    lean_dec(v_stop_1709_);
    v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___redArg(v_as_1707_, v_i_boxed_1716_, v_stop_boxed_1717_, v_b_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
    lean_dec(v___y_1714_);
    lean_dec_ref(v___y_1713_);
    lean_dec_ref(v___y_1712_);
    lean_dec(v___y_1711_);
    lean_dec_ref(v_as_1707_);
    return v_res_1718_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___lam__0(
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: usize = 0;
    let mut v___x_1742_: usize = 0;
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: usize = 0;
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1725_ =
                    l_Lean_Meta_getPropHyps(v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
                if lean_obj_tag(v___x_1725_) == 0 {
                    v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
                    v_isSharedCheck_1747_ = (!lean_is_exclusive(v___x_1725_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1728_ = v___x_1725_;
                        v_isShared_1729_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1726_);
                        lean_dec(v___x_1725_);
                        v___x_1728_ = lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1748_ = lean_ctor_get(v___x_1725_, 0);
                    v_isSharedCheck_1755_ = (!lean_is_exclusive(v___x_1725_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1750_ = v___x_1725_;
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1748_);
                        lean_dec(v___x_1725_);
                        v___x_1750_ = lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1730_ = lean_unsigned_to_nat(0);
                v___x_1731_ = lean_array_get_size(v_a_1726_);
                v___x_1732_ = lean_box(0);
                v___x_1733_ = lean_nat_dec_lt(v___x_1730_, v___x_1731_);
                if v___x_1733_ == 0 {
                    lean_dec(v_a_1726_);
                    if v_isShared_1729_ == 0 {
                        lean_ctor_set(v___x_1728_, 0, v___x_1732_);
                        v___x_1735_ = v___x_1728_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1732_);
                        v___x_1735_ = v_reuseFailAlloc_1736_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1737_ = lean_nat_dec_le(v___x_1731_, v___x_1731_);
                    if v___x_1737_ == 0 {
                        if v___x_1733_ == 0 {
                            lean_dec(v_a_1726_);
                            if v_isShared_1729_ == 0 {
                                lean_ctor_set(v___x_1728_, 0, v___x_1732_);
                                v___x_1739_ = v___x_1728_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1732_);
                                v___x_1739_ = v_reuseFailAlloc_1740_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1728_);
                            v___x_1741_ = 0usize;
                            v___x_1742_ = lean_usize_of_nat(v___x_1731_);
                            v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___redArg(v_a_1726_, v___x_1741_, v___x_1742_, v___x_1732_, v___y_1719_, v___y_1720_, v___y_1722_, v___y_1723_);
                            lean_dec(v_a_1726_);
                            return v___x_1743_;
                        }
                    } else {
                        lean_del_object(v___x_1728_);
                        v___x_1744_ = 0usize;
                        v___x_1745_ = lean_usize_of_nat(v___x_1731_);
                        v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___redArg(v_a_1726_, v___x_1744_, v___x_1745_, v___x_1732_, v___y_1719_, v___y_1720_, v___y_1722_, v___y_1723_);
                        lean_dec(v_a_1726_);
                        return v___x_1746_;
                    }
                }
            }
            2 => {
                return v___x_1735_;
            }
            3 => {
                return v___x_1739_;
            }
            4 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___lam__0___boxed(
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___lam__0(v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
    lean_dec(v___y_1760_);
    lean_dec_ref(v___y_1759_);
    lean_dec(v___y_1758_);
    lean_dec_ref(v___y_1757_);
    lean_dec(v___y_1756_);
    return v_res_1762_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal(
    mut v_goal_1764_: *mut LeanObject,
    mut v_a_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v___f_1771_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___closed__0;
    v___x_1772_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__1___redArg(v_goal_1764_, v___f_1771_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
    return v___x_1772_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal___boxed(
    mut v_goal_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
    mut v_a_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
    mut v_a_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1780_: *mut LeanObject = core::ptr::null_mut();
    v_res_1780_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal(v_goal_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
    lean_dec(v_a_1778_);
    lean_dec_ref(v_a_1777_);
    lean_dec(v_a_1776_);
    lean_dec_ref(v_a_1775_);
    lean_dec(v_a_1774_);
    return v_res_1780_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0(
    mut v_as_1781_: *mut LeanObject,
    mut v_i_1782_: usize,
    mut v_stop_1783_: usize,
    mut v_b_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___redArg(v_as_1781_, v_i_1782_, v_stop_1783_, v_b_1784_, v___y_1785_, v___y_1786_, v___y_1788_, v___y_1789_);
    return v___x_1791_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0___boxed(
    mut v_as_1792_: *mut LeanObject,
    mut v_i_1793_: *mut LeanObject,
    mut v_stop_1794_: *mut LeanObject,
    mut v_b_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1802_: usize = 0;
    let mut v_stop_boxed_1803_: usize = 0;
    let mut v_res_1804_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1802_ = lean_unbox_usize(v_i_1793_);
    lean_dec(v_i_1793_);
    v_stop_boxed_1803_ = lean_unbox_usize(v_stop_1794_);
    lean_dec(v_stop_1794_);
    v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal_spec__0(v_as_1792_, v_i_boxed_1802_, v_stop_boxed_1803_, v_b_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
    lean_dec(v___y_1800_);
    lean_dec_ref(v___y_1799_);
    lean_dec(v___y_1798_);
    lean_dec_ref(v___y_1797_);
    lean_dec(v___y_1796_);
    lean_dec_ref(v_as_1792_);
    return v_res_1804_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__0(
    mut v_sz_1805_: usize,
    mut v_i_1806_: usize,
    mut v_bs_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1808_: u8 = 0;
    let mut v_v_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyp_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: usize = 0;
    let mut v___x_1814_: usize = 0;
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1808_ = lean_usize_dec_lt(v_i_1806_, v_sz_1805_);
                if v___x_1808_ == 0 {
                    return v_bs_1807_;
                } else {
                    v_v_1809_ = lean_array_uget_borrowed(v_bs_1807_, v_i_1806_);
                    v_hyp_1810_ = lean_ctor_get(v_v_1809_, 0);
                    lean_inc_ref(v_hyp_1810_);
                    v___x_1811_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1812_ = lean_array_uset(v_bs_1807_, v_i_1806_, v___x_1811_);
                    v___x_1813_ = 1usize;
                    v___x_1814_ = lean_usize_add(v_i_1806_, v___x_1813_);
                    v___x_1815_ = lean_array_uset(v_bs_x27_1812_, v_i_1806_, v_hyp_1810_);
                    v_i_1806_ = v___x_1814_;
                    v_bs_1807_ = v___x_1815_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__0___boxed(
    mut v_sz_1817_: *mut LeanObject,
    mut v_i_1818_: *mut LeanObject,
    mut v_bs_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1820_: usize = 0;
    let mut v_i_boxed_1821_: usize = 0;
    let mut v_res_1822_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1820_ = lean_unbox_usize(v_sz_1817_);
    lean_dec(v_sz_1817_);
    v_i_boxed_1821_ = lean_unbox_usize(v_i_1818_);
    lean_dec(v_i_1818_);
    v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__0(v_sz_boxed_1820_, v_i_boxed_1821_, v_bs_1819_);
    return v_res_1822_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___redArg(
    mut v_a_1823_: *mut LeanObject,
    mut v_x_1824_: *mut LeanObject,
) -> u8 {
    let mut v___x_1825_: u8 = 0;
    let mut v_key_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1824_) == 0 {
                    v___x_1825_ = 0;
                    return v___x_1825_;
                } else {
                    v_key_1826_ = lean_ctor_get(v_x_1824_, 0);
                    v_tail_1827_ = lean_ctor_get(v_x_1824_, 2);
                    v___x_1828_ = l_Lean_instBEqFVarId_beq(v_key_1826_, v_a_1823_);
                    if v___x_1828_ == 0 {
                        v_x_1824_ = v_tail_1827_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1828_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___redArg___boxed(
    mut v_a_1830_: *mut LeanObject,
    mut v_x_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1832_: u8 = 0;
    let mut v_r_1833_: *mut LeanObject = core::ptr::null_mut();
    v_res_1832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___redArg(v_a_1830_, v_x_1831_);
    lean_dec(v_x_1831_);
    lean_dec(v_a_1830_);
    v_r_1833_ = lean_box((v_res_1832_) as usize);
    return v_r_1833_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_1834_: *mut LeanObject,
    mut v_x_1835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u64 = 0;
    let mut v___x_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v_fold_1846_: u64 = 0;
    let mut v___x_1847_: u64 = 0;
    let mut v___x_1848_: u64 = 0;
    let mut v___x_1849_: u64 = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: usize = 0;
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1835_) == 0 {
                    return v_x_1834_;
                } else {
                    v_key_1836_ = lean_ctor_get(v_x_1835_, 0);
                    v_value_1837_ = lean_ctor_get(v_x_1835_, 1);
                    v_tail_1838_ = lean_ctor_get(v_x_1835_, 2);
                    v_isSharedCheck_1861_ = (!lean_is_exclusive(v_x_1835_)) as u8;
                    if v_isSharedCheck_1861_ == 0 {
                        v___x_1840_ = v_x_1835_;
                        v_isShared_1841_ = v_isSharedCheck_1861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1838_);
                        lean_inc(v_value_1837_);
                        lean_inc(v_key_1836_);
                        lean_dec(v_x_1835_);
                        v___x_1840_ = lean_box(0);
                        v_isShared_1841_ = v_isSharedCheck_1861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1842_ = lean_array_get_size(v_x_1834_);
                v___x_1843_ = l_Lean_instHashableFVarId_hash(v_key_1836_);
                v___x_1844_ = 32u64;
                v___x_1845_ = lean_uint64_shift_right(v___x_1843_, v___x_1844_);
                v_fold_1846_ = lean_uint64_xor(v___x_1843_, v___x_1845_);
                v___x_1847_ = 16u64;
                v___x_1848_ = lean_uint64_shift_right(v_fold_1846_, v___x_1847_);
                v___x_1849_ = lean_uint64_xor(v_fold_1846_, v___x_1848_);
                v___x_1850_ = lean_uint64_to_usize(v___x_1849_);
                v___x_1851_ = lean_usize_of_nat(v___x_1842_);
                v___x_1852_ = 1usize;
                v___x_1853_ = lean_usize_sub(v___x_1851_, v___x_1852_);
                v___x_1854_ = lean_usize_land(v___x_1850_, v___x_1853_);
                v___x_1855_ = lean_array_uget_borrowed(v_x_1834_, v___x_1854_);
                lean_inc(v___x_1855_);
                if v_isShared_1841_ == 0 {
                    lean_ctor_set(v___x_1840_, 2, v___x_1855_);
                    v___x_1857_ = v___x_1840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_key_1836_);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_value_1837_);
                    lean_ctor_set(v_reuseFailAlloc_1860_, 2, v___x_1855_);
                    v___x_1857_ = v_reuseFailAlloc_1860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1858_ = lean_array_uset(v_x_1834_, v___x_1854_, v___x_1857_);
                v_x_1834_ = v___x_1858_;
                v_x_1835_ = v_tail_1838_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4___redArg(
    mut v_i_1862_: *mut LeanObject,
    mut v_source_1863_: *mut LeanObject,
    mut v_target_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v_es_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1865_ = lean_array_get_size(v_source_1863_);
                v___x_1866_ = lean_nat_dec_lt(v_i_1862_, v___x_1865_);
                if v___x_1866_ == 0 {
                    lean_dec_ref(v_source_1863_);
                    lean_dec(v_i_1862_);
                    return v_target_1864_;
                } else {
                    v_es_1867_ = lean_array_fget(v_source_1863_, v_i_1862_);
                    v___x_1868_ = lean_box(0);
                    v_source_1869_ = lean_array_fset(v_source_1863_, v_i_1862_, v___x_1868_);
                    v_target_1870_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4_spec__6___redArg(v_target_1864_, v_es_1867_);
                    v___x_1871_ = lean_unsigned_to_nat(1);
                    v___x_1872_ = lean_nat_add(v_i_1862_, v___x_1871_);
                    lean_dec(v_i_1862_);
                    v_i_1862_ = v___x_1872_;
                    v_source_1863_ = v_source_1869_;
                    v_target_1864_ = v_target_1870_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3___redArg(
    mut v_data_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = lean_array_get_size(v_data_1874_);
    v___x_1876_ = lean_unsigned_to_nat(2);
    v_nbuckets_1877_ = lean_nat_mul(v___x_1875_, v___x_1876_);
    v___x_1878_ = lean_unsigned_to_nat(0);
    v___x_1879_ = lean_box(0);
    v___x_1880_ = lean_mk_array(v_nbuckets_1877_, v___x_1879_);
    v___x_1881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4___redArg(v___x_1878_, v_data_1874_, v___x_1880_);
    return v___x_1881_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2___redArg(
    mut v_m_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v_b_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: u64 = 0;
    let mut v___x_1889_: u64 = 0;
    let mut v___x_1890_: u64 = 0;
    let mut v_fold_1891_: u64 = 0;
    let mut v___x_1892_: u64 = 0;
    let mut v___x_1893_: u64 = 0;
    let mut v___x_1894_: u64 = 0;
    let mut v___x_1895_: usize = 0;
    let mut v___x_1896_: usize = 0;
    let mut v___x_1897_: usize = 0;
    let mut v___x_1898_: usize = 0;
    let mut v___x_1899_: usize = 0;
    let mut v_bkt_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v_val_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1922_: u8 = 0;
    let mut v_unused_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1885_ = lean_ctor_get(v_m_1882_, 0);
                v_buckets_1886_ = lean_ctor_get(v_m_1882_, 1);
                v___x_1887_ = lean_array_get_size(v_buckets_1886_);
                v___x_1888_ = l_Lean_instHashableFVarId_hash(v_a_1883_);
                v___x_1889_ = 32u64;
                v___x_1890_ = lean_uint64_shift_right(v___x_1888_, v___x_1889_);
                v_fold_1891_ = lean_uint64_xor(v___x_1888_, v___x_1890_);
                v___x_1892_ = 16u64;
                v___x_1893_ = lean_uint64_shift_right(v_fold_1891_, v___x_1892_);
                v___x_1894_ = lean_uint64_xor(v_fold_1891_, v___x_1893_);
                v___x_1895_ = lean_uint64_to_usize(v___x_1894_);
                v___x_1896_ = lean_usize_of_nat(v___x_1887_);
                v___x_1897_ = 1usize;
                v___x_1898_ = lean_usize_sub(v___x_1896_, v___x_1897_);
                v___x_1899_ = lean_usize_land(v___x_1895_, v___x_1898_);
                v_bkt_1900_ = lean_array_uget_borrowed(v_buckets_1886_, v___x_1899_);
                v___x_1901_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___redArg(v_a_1883_, v_bkt_1900_);
                if v___x_1901_ == 0 {
                    lean_inc_ref(v_buckets_1886_);
                    lean_inc(v_size_1885_);
                    v_isSharedCheck_1922_ = (!lean_is_exclusive(v_m_1882_)) as u8;
                    if v_isSharedCheck_1922_ == 0 {
                        v_unused_1923_ = lean_ctor_get(v_m_1882_, 1);
                        lean_dec(v_unused_1923_);
                        v_unused_1924_ = lean_ctor_get(v_m_1882_, 0);
                        lean_dec(v_unused_1924_);
                        v___x_1903_ = v_m_1882_;
                        v_isShared_1904_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1882_);
                        v___x_1903_ = lean_box(0);
                        v_isShared_1904_ = v_isSharedCheck_1922_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1884_);
                    lean_dec(v_a_1883_);
                    return v_m_1882_;
                }
            }
            1 => {
                v___x_1905_ = lean_unsigned_to_nat(1);
                v_size_x27_1906_ = lean_nat_add(v_size_1885_, v___x_1905_);
                lean_dec(v_size_1885_);
                lean_inc(v_bkt_1900_);
                v___x_1907_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1907_, 0, v_a_1883_);
                lean_ctor_set(v___x_1907_, 1, v_b_1884_);
                lean_ctor_set(v___x_1907_, 2, v_bkt_1900_);
                v_buckets_x27_1908_ = lean_array_uset(v_buckets_1886_, v___x_1899_, v___x_1907_);
                v___x_1909_ = lean_unsigned_to_nat(4);
                v___x_1910_ = lean_nat_mul(v_size_x27_1906_, v___x_1909_);
                v___x_1911_ = lean_unsigned_to_nat(3);
                v___x_1912_ = lean_nat_div(v___x_1910_, v___x_1911_);
                lean_dec(v___x_1910_);
                v___x_1913_ = lean_array_get_size(v_buckets_x27_1908_);
                v___x_1914_ = lean_nat_dec_le(v___x_1912_, v___x_1913_);
                lean_dec(v___x_1912_);
                if v___x_1914_ == 0 {
                    v_val_1915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3___redArg(v_buckets_x27_1908_);
                    if v_isShared_1904_ == 0 {
                        lean_ctor_set(v___x_1903_, 1, v_val_1915_);
                        lean_ctor_set(v___x_1903_, 0, v_size_x27_1906_);
                        v___x_1917_ = v___x_1903_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_size_x27_1906_);
                        lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_val_1915_);
                        v___x_1917_ = v_reuseFailAlloc_1918_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1904_ == 0 {
                        lean_ctor_set(v___x_1903_, 1, v_buckets_x27_1908_);
                        lean_ctor_set(v___x_1903_, 0, v_size_x27_1906_);
                        v___x_1920_ = v___x_1903_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_size_x27_1906_);
                        lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_buckets_x27_1908_);
                        v___x_1920_ = v_reuseFailAlloc_1921_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1917_;
            }
            3 => {
                return v___x_1920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___redArg(
    mut v_m_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u64 = 0;
    let mut v___x_1930_: u64 = 0;
    let mut v___x_1931_: u64 = 0;
    let mut v_fold_1932_: u64 = 0;
    let mut v___x_1933_: u64 = 0;
    let mut v___x_1934_: u64 = 0;
    let mut v___x_1935_: u64 = 0;
    let mut v___x_1936_: usize = 0;
    let mut v___x_1937_: usize = 0;
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: usize = 0;
    let mut v___x_1940_: usize = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    v_buckets_1927_ = lean_ctor_get(v_m_1925_, 1);
    v___x_1928_ = lean_array_get_size(v_buckets_1927_);
    v___x_1929_ = l_Lean_instHashableFVarId_hash(v_a_1926_);
    v___x_1930_ = 32u64;
    v___x_1931_ = lean_uint64_shift_right(v___x_1929_, v___x_1930_);
    v_fold_1932_ = lean_uint64_xor(v___x_1929_, v___x_1931_);
    v___x_1933_ = 16u64;
    v___x_1934_ = lean_uint64_shift_right(v_fold_1932_, v___x_1933_);
    v___x_1935_ = lean_uint64_xor(v_fold_1932_, v___x_1934_);
    v___x_1936_ = lean_uint64_to_usize(v___x_1935_);
    v___x_1937_ = lean_usize_of_nat(v___x_1928_);
    v___x_1938_ = 1usize;
    v___x_1939_ = lean_usize_sub(v___x_1937_, v___x_1938_);
    v___x_1940_ = lean_usize_land(v___x_1936_, v___x_1939_);
    v___x_1941_ = lean_array_uget_borrowed(v_buckets_1927_, v___x_1940_);
    v___x_1942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___redArg(v_a_1926_, v___x_1941_);
    return v___x_1942_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___redArg___boxed(
    mut v_m_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: u8 = 0;
    let mut v_r_1946_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___redArg(v_m_1943_, v_a_1944_);
    lean_dec(v_a_1944_);
    lean_dec_ref(v_m_1943_);
    v_r_1946_ = lean_box((v_res_1945_) as usize);
    return v_r_1946_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg___lam__0(
    mut v_original_1947_: *mut LeanObject,
    mut v___x_1948_: *mut LeanObject,
    mut v___x_1949_: *mut LeanObject,
    mut v_____r_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1958_ = lean_st_ref_get(v___y_1952_);
                v_acNfCache_1959_ = lean_ctor_get(v___x_1958_, 1);
                lean_inc_ref(v_acNfCache_1959_);
                lean_dec(v___x_1958_);
                v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___redArg(v_acNfCache_1959_, v_original_1947_);
                lean_dec_ref(v_acNfCache_1959_);
                if v___x_1960_ == 0 {
                    lean_dec(v___x_1949_);
                    v___x_1961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1961_, 0, v___x_1948_);
                    v___x_1962_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1962_, 0, v___x_1961_);
                    return v___x_1962_;
                } else {
                    v___x_1963_ = lean_st_ref_take(v___y_1952_);
                    v_rewriteCache_1964_ = lean_ctor_get(v___x_1963_, 0);
                    v_acNfCache_1965_ = lean_ctor_get(v___x_1963_, 1);
                    v_typeAnalysis_1966_ = lean_ctor_get(v___x_1963_, 2);
                    v_isSharedCheck_1977_ = (!lean_is_exclusive(v___x_1963_)) as u8;
                    if v_isSharedCheck_1977_ == 0 {
                        v___x_1968_ = v___x_1963_;
                        v_isShared_1969_ = v_isSharedCheck_1977_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_typeAnalysis_1966_);
                        lean_inc(v_acNfCache_1965_);
                        lean_inc(v_rewriteCache_1964_);
                        lean_dec(v___x_1963_);
                        v___x_1968_ = lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1977_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1970_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2___redArg(v_acNfCache_1965_, v___x_1949_, v___x_1948_);
                if v_isShared_1969_ == 0 {
                    lean_ctor_set(v___x_1968_, 1, v___x_1970_);
                    v___x_1972_ = v___x_1968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_rewriteCache_1964_);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1970_);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_typeAnalysis_1966_);
                    v___x_1972_ = v_reuseFailAlloc_1976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1973_ = lean_st_ref_set(v___y_1952_, v___x_1972_);
                v___x_1974_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1974_, 0, v___x_1948_);
                v___x_1975_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1975_, 0, v___x_1974_);
                return v___x_1975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg___lam__0___boxed(
    mut v_original_1978_: *mut LeanObject,
    mut v___x_1979_: *mut LeanObject,
    mut v___x_1980_: *mut LeanObject,
    mut v_____r_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1989_: *mut LeanObject = core::ptr::null_mut();
    v_res_1989_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg___lam__0(v_original_1978_, v___x_1979_, v___x_1980_, v_____r_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
    lean_dec(v___y_1987_);
    lean_dec_ref(v___y_1986_);
    lean_dec(v___y_1985_);
    lean_dec_ref(v___y_1984_);
    lean_dec(v___y_1983_);
    lean_dec_ref(v___y_1982_);
    lean_dec(v_original_1978_);
    return v_res_1989_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg(
    mut v_upperBound_1990_: *mut LeanObject,
    mut v_hypsToAdd_1991_: *mut LeanObject,
    mut v_fst_1992_: *mut LeanObject,
    mut v_a_1993_: *mut LeanObject,
    mut v_b_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut v_a_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_original_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2025_ = lean_nat_dec_lt(v_a_1993_, v_upperBound_1990_);
                if v___x_2025_ == 0 {
                    lean_dec(v_a_1993_);
                    v___x_2026_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2026_, 0, v_b_1994_);
                    return v___x_2026_;
                } else {
                    v___x_2027_ = lean_st_ref_get(v___y_1996_);
                    v___x_2028_ = lean_array_fget_borrowed(v_hypsToAdd_1991_, v_a_1993_);
                    v_original_2029_ = lean_ctor_get(v___x_2028_, 1);
                    v_rewriteCache_2030_ = lean_ctor_get(v___x_2027_, 0);
                    lean_inc_ref(v_rewriteCache_2030_);
                    lean_dec(v___x_2027_);
                    v___x_2031_ = lean_box(0);
                    v___x_2032_ = lean_box(0);
                    v___x_2033_ = lean_array_get_borrowed(v___x_2032_, v_fst_1992_, v_a_1993_);
                    v___x_2034_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___redArg(v_rewriteCache_2030_, v_original_2029_);
                    lean_dec_ref(v_rewriteCache_2030_);
                    if v___x_2034_ == 0 {
                        lean_inc(v___x_2033_);
                        v___x_2035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg___lam__0(v_original_2029_, v___x_2031_, v___x_2033_, v___x_2031_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
                        v___y_2003_ = v___x_2035_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2036_ = lean_st_ref_take(v___y_1996_);
                        v_rewriteCache_2037_ = lean_ctor_get(v___x_2036_, 0);
                        v_acNfCache_2038_ = lean_ctor_get(v___x_2036_, 1);
                        v_typeAnalysis_2039_ = lean_ctor_get(v___x_2036_, 2);
                        v_isSharedCheck_2049_ = (!lean_is_exclusive(v___x_2036_)) as u8;
                        if v_isSharedCheck_2049_ == 0 {
                            v___x_2041_ = v___x_2036_;
                            v_isShared_2042_ = v_isSharedCheck_2049_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_typeAnalysis_2039_);
                            lean_inc(v_acNfCache_2038_);
                            lean_inc(v_rewriteCache_2037_);
                            lean_dec(v___x_2036_);
                            v___x_2041_ = lean_box(0);
                            v_isShared_2042_ = v_isSharedCheck_2049_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_2003_) == 0 {
                    v_a_2004_ = lean_ctor_get(v___y_2003_, 0);
                    v_isSharedCheck_2016_ = (!lean_is_exclusive(v___y_2003_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2006_ = v___y_2003_;
                        v_isShared_2007_ = v_isSharedCheck_2016_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2004_);
                        lean_dec(v___y_2003_);
                        v___x_2006_ = lean_box(0);
                        v_isShared_2007_ = v_isSharedCheck_2016_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1993_);
                    v_a_2017_ = lean_ctor_get(v___y_2003_, 0);
                    v_isSharedCheck_2024_ = (!lean_is_exclusive(v___y_2003_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_2019_ = v___y_2003_;
                        v_isShared_2020_ = v_isSharedCheck_2024_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2017_);
                        lean_dec(v___y_2003_);
                        v___x_2019_ = lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2024_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2004_) == 0 {
                    lean_dec(v_a_1993_);
                    v_a_2008_ = lean_ctor_get(v_a_2004_, 0);
                    lean_inc(v_a_2008_);
                    lean_dec_ref_known(v_a_2004_, 1);
                    if v_isShared_2007_ == 0 {
                        lean_ctor_set(v___x_2006_, 0, v_a_2008_);
                        v___x_2010_ = v___x_2006_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2008_);
                        v___x_2010_ = v_reuseFailAlloc_2011_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2006_);
                    v_a_2012_ = lean_ctor_get(v_a_2004_, 0);
                    lean_inc(v_a_2012_);
                    lean_dec_ref_known(v_a_2004_, 1);
                    v___x_2013_ = lean_unsigned_to_nat(1);
                    v___x_2014_ = lean_nat_add(v_a_1993_, v___x_2013_);
                    lean_dec(v_a_1993_);
                    v_a_1993_ = v___x_2014_;
                    v_b_1994_ = v_a_2012_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_2010_;
            }
            4 => {
                if v_isShared_2020_ == 0 {
                    v___x_2022_ = v___x_2019_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2022_;
            }
            6 => {
                lean_inc(v___x_2033_);
                v___x_2043_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2___redArg(v_rewriteCache_2037_, v___x_2033_, v___x_2031_);
                if v_isShared_2042_ == 0 {
                    lean_ctor_set(v___x_2041_, 0, v___x_2043_);
                    v___x_2045_ = v___x_2041_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2043_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_acNfCache_2038_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_typeAnalysis_2039_);
                    v___x_2045_ = v_reuseFailAlloc_2048_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2046_ = lean_st_ref_set(v___y_1996_, v___x_2045_);
                lean_inc(v___x_2033_);
                v___x_2047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg___lam__0(v_original_2029_, v___x_2031_, v___x_2033_, v___x_2031_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
                v___y_2003_ = v___x_2047_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg___boxed(
    mut v_upperBound_2050_: *mut LeanObject,
    mut v_hypsToAdd_2051_: *mut LeanObject,
    mut v_fst_2052_: *mut LeanObject,
    mut v_a_2053_: *mut LeanObject,
    mut v_b_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2062_: *mut LeanObject = core::ptr::null_mut();
    v_res_2062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg(v_upperBound_2050_, v_hypsToAdd_2051_, v_fst_2052_, v_a_2053_, v_b_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
    lean_dec(v___y_2060_);
    lean_dec_ref(v___y_2059_);
    lean_dec(v___y_2058_);
    lean_dec_ref(v___y_2057_);
    lean_dec(v___y_2056_);
    lean_dec_ref(v___y_2055_);
    lean_dec_ref(v_fst_2052_);
    lean_dec_ref(v_hypsToAdd_2051_);
    lean_dec(v_upperBound_2050_);
    return v_res_2062_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = lean_box(0);
    v___x_2066_ = lean_unsigned_to_nat(16);
    v___x_2067_ = lean_mk_array(v___x_2066_, v___x_2065_);
    return v___x_2067_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    v___x_2068_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1,
    );
    v___x_2069_ = lean_unsigned_to_nat(0);
    v___x_2070_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2070_, 0, v___x_2069_);
    lean_ctor_set(v___x_2070_, 1, v___x_2068_);
    return v___x_2070_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    v___x_2071_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__2,
    );
    v___x_2072_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0;
    v___x_2073_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2073_, 0, v___x_2072_);
    lean_ctor_set(v___x_2073_, 1, v___x_2072_);
    lean_ctor_set(v___x_2073_, 2, v___x_2071_);
    return v___x_2073_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(
    mut v_goal_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2088_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToDelete_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsToAdd_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v_sz_2094_: usize = 0;
    let mut v___x_2095_: usize = 0;
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2112_: u8 = 0;
    let mut v_a_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_a_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_a_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2132_: u8 = 0;
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut v_unused_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2082_ = lean_unsigned_to_nat(0);
                v___x_2083_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__3);
                v___x_2084_ = lean_st_mk_ref(v___x_2083_);
                lean_inc(v_goal_2074_);
                v___x_2085_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processGoal(v_goal_2074_, v___x_2084_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
                if lean_obj_tag(v___x_2085_) == 0 {
                    v_isSharedCheck_2141_ = (!lean_is_exclusive(v___x_2085_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v_unused_2142_ = lean_ctor_get(v___x_2085_, 0);
                        lean_dec(v_unused_2142_);
                        v___x_2087_ = v___x_2085_;
                        v_isShared_2088_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2085_);
                        v___x_2087_ = lean_box(0);
                        v_isShared_2088_ = v_isSharedCheck_2141_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2084_);
                    lean_dec(v_goal_2074_);
                    v_a_2143_ = lean_ctor_get(v___x_2085_, 0);
                    v_isSharedCheck_2150_ = (!lean_is_exclusive(v___x_2085_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2145_ = v___x_2085_;
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2143_);
                        lean_dec(v___x_2085_);
                        v___x_2145_ = lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2089_ = lean_st_ref_get(v___x_2084_);
                lean_dec(v___x_2084_);
                v_hypsToDelete_2090_ = lean_ctor_get(v___x_2089_, 0);
                lean_inc_ref(v_hypsToDelete_2090_);
                v_hypsToAdd_2091_ = lean_ctor_get(v___x_2089_, 1);
                lean_inc_ref(v_hypsToAdd_2091_);
                lean_dec(v___x_2089_);
                v___x_2092_ = lean_array_get_size(v_hypsToAdd_2091_);
                v___x_2093_ = lean_nat_dec_eq(v___x_2092_, v___x_2082_);
                if v___x_2093_ == 0 {
                    lean_del_object(v___x_2087_);
                    v_sz_2094_ = lean_array_size(v_hypsToAdd_2091_);
                    v___x_2095_ = 0usize;
                    lean_inc_ref(v_hypsToAdd_2091_);
                    v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__0(v_sz_2094_, v___x_2095_, v_hypsToAdd_2091_);
                    v___x_2097_ = l_Lean_MVarId_assertHypotheses(
                        v_goal_2074_,
                        v___x_2096_,
                        v___y_2077_,
                        v___y_2078_,
                        v___y_2079_,
                        v___y_2080_,
                    );
                    if lean_obj_tag(v___x_2097_) == 0 {
                        v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
                        lean_inc(v_a_2098_);
                        lean_dec_ref_known(v___x_2097_, 1);
                        v_fst_2099_ = lean_ctor_get(v_a_2098_, 0);
                        lean_inc(v_fst_2099_);
                        v_snd_2100_ = lean_ctor_get(v_a_2098_, 1);
                        lean_inc(v_snd_2100_);
                        lean_dec(v_a_2098_);
                        v___x_2101_ = lean_box(0);
                        v___x_2102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg(v___x_2092_, v_hypsToAdd_2091_, v_fst_2099_, v___x_2082_, v___x_2101_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
                        lean_dec(v_fst_2099_);
                        lean_dec_ref(v_hypsToAdd_2091_);
                        if lean_obj_tag(v___x_2102_) == 0 {
                            lean_dec_ref_known(v___x_2102_, 1);
                            v___x_2103_ = l_Lean_MVarId_tryClearMany(
                                v_snd_2100_,
                                v_hypsToDelete_2090_,
                                v___y_2077_,
                                v___y_2078_,
                                v___y_2079_,
                                v___y_2080_,
                            );
                            lean_dec_ref(v_hypsToDelete_2090_);
                            if lean_obj_tag(v___x_2103_) == 0 {
                                v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
                                v_isSharedCheck_2112_ = (!lean_is_exclusive(v___x_2103_)) as u8;
                                if v_isSharedCheck_2112_ == 0 {
                                    v___x_2106_ = v___x_2103_;
                                    v_isShared_2107_ = v_isSharedCheck_2112_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_2104_);
                                    lean_dec(v___x_2103_);
                                    v___x_2106_ = lean_box(0);
                                    v_isShared_2107_ = v_isSharedCheck_2112_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_2113_ = lean_ctor_get(v___x_2103_, 0);
                                v_isSharedCheck_2120_ = (!lean_is_exclusive(v___x_2103_)) as u8;
                                if v_isSharedCheck_2120_ == 0 {
                                    v___x_2115_ = v___x_2103_;
                                    v_isShared_2116_ = v_isSharedCheck_2120_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2113_);
                                    lean_dec(v___x_2103_);
                                    v___x_2115_ = lean_box(0);
                                    v_isShared_2116_ = v_isSharedCheck_2120_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_2100_);
                            lean_dec_ref(v_hypsToDelete_2090_);
                            v_a_2121_ = lean_ctor_get(v___x_2102_, 0);
                            v_isSharedCheck_2128_ = (!lean_is_exclusive(v___x_2102_)) as u8;
                            if v_isSharedCheck_2128_ == 0 {
                                v___x_2123_ = v___x_2102_;
                                v_isShared_2124_ = v_isSharedCheck_2128_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2121_);
                                lean_dec(v___x_2102_);
                                v___x_2123_ = lean_box(0);
                                v_isShared_2124_ = v_isSharedCheck_2128_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_hypsToAdd_2091_);
                        lean_dec_ref(v_hypsToDelete_2090_);
                        v_a_2129_ = lean_ctor_get(v___x_2097_, 0);
                        v_isSharedCheck_2136_ = (!lean_is_exclusive(v___x_2097_)) as u8;
                        if v_isSharedCheck_2136_ == 0 {
                            v___x_2131_ = v___x_2097_;
                            v_isShared_2132_ = v_isSharedCheck_2136_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2129_);
                            lean_dec(v___x_2097_);
                            v___x_2131_ = lean_box(0);
                            v_isShared_2132_ = v_isSharedCheck_2136_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_hypsToAdd_2091_);
                    lean_dec_ref(v_hypsToDelete_2090_);
                    v___x_2137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2137_, 0, v_goal_2074_);
                    if v_isShared_2088_ == 0 {
                        lean_ctor_set(v___x_2087_, 0, v___x_2137_);
                        v___x_2139_ = v___x_2087_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
                        v___x_2139_ = v_reuseFailAlloc_2140_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2108_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2108_, 0, v_a_2104_);
                if v_isShared_2107_ == 0 {
                    lean_ctor_set(v___x_2106_, 0, v___x_2108_);
                    v___x_2110_ = v___x_2106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
                    v___x_2110_ = v_reuseFailAlloc_2111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2110_;
            }
            4 => {
                if v_isShared_2116_ == 0 {
                    v___x_2118_ = v___x_2115_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
                    v___x_2118_ = v_reuseFailAlloc_2119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2118_;
            }
            6 => {
                if v_isShared_2124_ == 0 {
                    v___x_2126_ = v___x_2123_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
                    v___x_2126_ = v_reuseFailAlloc_2127_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2126_;
            }
            8 => {
                if v_isShared_2132_ == 0 {
                    v___x_2134_ = v___x_2131_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
                    v___x_2134_ = v_reuseFailAlloc_2135_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2134_;
            }
            10 => {
                return v___x_2139_;
            }
            11 => {
                if v_isShared_2146_ == 0 {
                    v___x_2148_ = v___x_2145_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed(
    mut v_goal_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2159_: *mut LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(
        v_goal_2151_,
        v___y_2152_,
        v___y_2153_,
        v___y_2154_,
        v___y_2155_,
        v___y_2156_,
        v___y_2157_,
    );
    lean_dec(v___y_2157_);
    lean_dec_ref(v___y_2156_);
    lean_dec(v___y_2155_);
    lean_dec_ref(v___y_2154_);
    lean_dec(v___y_2153_);
    lean_dec_ref(v___y_2152_);
    return v_res_2159_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1(
    mut v_00_u03b2_2168_: *mut LeanObject,
    mut v_m_2169_: *mut LeanObject,
    mut v_a_2170_: *mut LeanObject,
) -> u8 {
    let mut v___x_2171_: u8 = 0;
    v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___redArg(v_m_2169_, v_a_2170_);
    return v___x_2171_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1___boxed(
    mut v_00_u03b2_2172_: *mut LeanObject,
    mut v_m_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2175_: u8 = 0;
    let mut v_r_2176_: *mut LeanObject = core::ptr::null_mut();
    v_res_2175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1(v_00_u03b2_2172_, v_m_2173_, v_a_2174_);
    lean_dec(v_a_2174_);
    lean_dec_ref(v_m_2173_);
    v_r_2176_ = lean_box((v_res_2175_) as usize);
    return v_r_2176_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2(
    mut v_00_u03b2_2177_: *mut LeanObject,
    mut v_m_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
    mut v_b_2180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v___x_2181_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2___redArg(v_m_2178_, v_a_2179_, v_b_2180_);
    return v___x_2181_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3(
    mut v_upperBound_2182_: *mut LeanObject,
    mut v_hypsToAdd_2183_: *mut LeanObject,
    mut v_fst_2184_: *mut LeanObject,
    mut v_inst_2185_: *mut LeanObject,
    mut v_R_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
    mut v_b_2188_: *mut LeanObject,
    mut v_c_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___redArg(v_upperBound_2182_, v_hypsToAdd_2183_, v_fst_2184_, v_a_2187_, v_b_2188_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
    return v___x_2197_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3___boxed(
    mut v_upperBound_2198_: *mut LeanObject,
    mut v_hypsToAdd_2199_: *mut LeanObject,
    mut v_fst_2200_: *mut LeanObject,
    mut v_inst_2201_: *mut LeanObject,
    mut v_R_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_b_2204_: *mut LeanObject,
    mut v_c_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2213_: *mut LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__3(v_upperBound_2198_, v_hypsToAdd_2199_, v_fst_2200_, v_inst_2201_, v_R_2202_, v_a_2203_, v_b_2204_, v_c_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
    lean_dec(v___y_2211_);
    lean_dec_ref(v___y_2210_);
    lean_dec(v___y_2209_);
    lean_dec_ref(v___y_2208_);
    lean_dec(v___y_2207_);
    lean_dec_ref(v___y_2206_);
    lean_dec_ref(v_fst_2200_);
    lean_dec_ref(v_hypsToAdd_2199_);
    lean_dec(v_upperBound_2198_);
    return v_res_2213_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1(
    mut v_00_u03b2_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_x_2216_: *mut LeanObject,
) -> u8 {
    let mut v___x_2217_: u8 = 0;
    v___x_2217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___redArg(v_a_2215_, v_x_2216_);
    return v___x_2217_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1___boxed(
    mut v_00_u03b2_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
    mut v_x_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2221_: u8 = 0;
    let mut v_r_2222_: *mut LeanObject = core::ptr::null_mut();
    v_res_2221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__1_spec__1(v_00_u03b2_2218_, v_a_2219_, v_x_2220_);
    lean_dec(v_x_2220_);
    lean_dec(v_a_2219_);
    v_r_2222_ = lean_box((v_res_2221_) as usize);
    return v_r_2222_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3(
    mut v_00_u03b2_2223_: *mut LeanObject,
    mut v_data_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    v___x_2225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3___redArg(v_data_2224_);
    return v___x_2225_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2226_: *mut LeanObject,
    mut v_i_2227_: *mut LeanObject,
    mut v_source_2228_: *mut LeanObject,
    mut v_target_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4___redArg(v_i_2227_, v_source_2228_, v_target_2229_);
    return v___x_2230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_2231_: *mut LeanObject,
    mut v_x_2232_: *mut LeanObject,
    mut v_x_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    v___x_2234_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_spec__2_spec__3_spec__4_spec__6___redArg(v_x_2232_, v_x_2233_);
    return v___x_2234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
}
