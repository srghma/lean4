// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Lambda
// Imports: Lean.Meta.Sym.Simp.SimpM
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_bvar___override, l_Lean_mkApp3, l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkAppB,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkLambda,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_mkRflResultCD,
    l_Lean_Meta_Sym_Simp_simp___boxed, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_infer_type;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 105, 102, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,2642306550782628284 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [81, 117, 111, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,14456664134214385499 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [102, 39, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12997779882188056240 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [103, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value) as *mut crate::leanh::LeanObject,2090554241476529182 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [102, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value) as *mut crate::leanh::LeanObject,1707590486618227741 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_simpLambda___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_simp___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_simpLambda___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpLambda___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1176_ = l_Lean_Expr_bvar___override(v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1178_ = l_Lean_Expr_bvar___override(v___x_1177_);
    return v___x_1178_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(
    mut v___x_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v___x_1186_: *mut crate::leanh::LeanObject,
    mut v_xs_1187_: *mut crate::leanh::LeanObject,
    mut v___x_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v___x_1191_: *mut crate::leanh::LeanObject,
    mut v___x_1192_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1193_: *mut crate::leanh::LeanObject,
    mut v___x_1194_: u8,
    mut v___x_1195_: u8,
    mut v___x_1196_: u8,
    mut v___x_1197_: *mut crate::leanh::LeanObject,
    mut v_f_1198_: *mut crate::leanh::LeanObject,
    mut v_g_1199_: *mut crate::leanh::LeanObject,
    mut v_h_1200_: *mut crate::leanh::LeanObject,
    mut v___x_1201_: *mut crate::leanh::LeanObject,
    mut v_f_x27_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0;
    crate::leanh::lean_inc_ref(v___x_1184_);
    v___x_1209_ = l_Lean_Name_mkStr2(v___x_1184_, v___x_1208_);
    crate::leanh::lean_inc(v_a_1185_);
    v___x_1210_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1210_, 0, v_a_1185_);
    crate::leanh::lean_ctor_set(v___x_1210_, 1, v___x_1186_);
    v___x_1211_ = l_Lean_mkConst(v___x_1209_, v___x_1210_);
    v___x_1212_ = 0;
    v___x_1213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1);
    v___x_1214_ = l_Lean_mkAppN(v___x_1213_, v_xs_1187_);
    crate::leanh::lean_inc_ref(v___x_1214_);
    crate::leanh::lean_inc_ref_n(v_a_1189_, 4);
    crate::leanh::lean_inc(v___x_1188_);
    v___x_1215_ = l_Lean_mkLambda(v___x_1188_, v___x_1212_, v_a_1189_, v___x_1214_);
    v___x_1216_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2);
    crate::leanh::lean_inc_ref_n(v_a_1190_, 2);
    v___x_1218_ = l_Lean_mkAppB(v_a_1190_, v___x_1217_, v___x_1213_);
    v___x_1219_ = l_Lean_mkLambda(v___x_1191_, v___x_1212_, v___x_1218_, v___x_1214_);
    v___x_1220_ = l_Lean_mkLambda(v___x_1192_, v___x_1212_, v_a_1189_, v___x_1219_);
    v___x_1221_ = l_Lean_mkLambda(v___x_1188_, v___x_1212_, v_a_1189_, v___x_1220_);
    crate::leanh::lean_inc_ref(v_f_x27_1202_);
    v___x_1222_ = l_Lean_mkApp6(
        v___x_1211_,
        v_a_1189_,
        v_a_1190_,
        v_00_u03b2_1193_,
        v___x_1215_,
        v___x_1221_,
        v_f_x27_1202_,
    );
    v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1216_);
    v___x_1224_ = lean_array_push(v___x_1223_, v_f_x27_1202_);
    v___x_1225_ = l_Array_append___redArg(v___x_1224_, v_xs_1187_);
    v___x_1226_ = l_Lean_Meta_mkLambdaFVars(
        v___x_1225_,
        v___x_1222_,
        v___x_1194_,
        v___x_1195_,
        v___x_1194_,
        v___x_1195_,
        v___x_1196_,
        v___y_1203_,
        v___y_1204_,
        v___y_1205_,
        v___y_1206_,
    );
    crate::leanh::lean_dec_ref(v___x_1225_);
    if crate::leanh::lean_obj_tag(v___x_1226_) == 0 {
        let mut v_a_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1227_ = crate::leanh::lean_ctor_get(v___x_1226_, 0);
        crate::leanh::lean_inc(v_a_1227_);
        crate::leanh::lean_dec_ref_known(v___x_1226_, 1);
        v___x_1228_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3;
        crate::leanh::lean_inc_ref(v___x_1184_);
        v___x_1229_ = l_Lean_Name_mkStr2(v___x_1184_, v___x_1228_);
        crate::leanh::lean_inc_n(v___x_1197_, 2);
        v___x_1230_ = l_Lean_mkConst(v___x_1229_, v___x_1197_);
        crate::leanh::lean_inc_ref(v_h_1200_);
        crate::leanh::lean_inc_ref_n(v_g_1199_, 2);
        crate::leanh::lean_inc_ref_n(v_f_1198_, 2);
        crate::leanh::lean_inc_ref_n(v_a_1190_, 2);
        crate::leanh::lean_inc_ref_n(v_a_1189_, 3);
        v___x_1231_ = l_Lean_mkApp5(
            v___x_1230_,
            v_a_1189_,
            v_a_1190_,
            v_f_1198_,
            v_g_1199_,
            v_h_1200_,
        );
        v___x_1232_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4;
        v___x_1233_ = l_Lean_Name_mkStr2(v___x_1184_, v___x_1232_);
        v___x_1234_ = l_Lean_mkConst(v___x_1233_, v___x_1197_);
        crate::leanh::lean_inc_ref(v___x_1234_);
        v___x_1235_ = l_Lean_mkApp3(v___x_1234_, v_a_1189_, v_a_1190_, v_f_1198_);
        v___x_1236_ = l_Lean_mkApp3(v___x_1234_, v_a_1189_, v_a_1190_, v_g_1199_);
        v___x_1237_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6;
        v___x_1238_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1238_, 0, v_a_1185_);
        crate::leanh::lean_ctor_set(v___x_1238_, 1, v___x_1197_);
        v___x_1239_ = l_Lean_mkConst(v___x_1237_, v___x_1238_);
        v___x_1240_ = l_Lean_mkApp6(
            v___x_1239_,
            v___x_1201_,
            v_a_1189_,
            v___x_1235_,
            v___x_1236_,
            v_a_1227_,
            v___x_1231_,
        );
        v___x_1241_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1242_ = lean_mk_empty_array_with_capacity(v___x_1241_);
        v___x_1243_ = lean_array_push(v___x_1242_, v_f_1198_);
        v___x_1244_ = lean_array_push(v___x_1243_, v_g_1199_);
        v___x_1245_ = lean_array_push(v___x_1244_, v_h_1200_);
        v___x_1246_ = l_Lean_Meta_mkLambdaFVars(
            v___x_1245_,
            v___x_1240_,
            v___x_1194_,
            v___x_1195_,
            v___x_1194_,
            v___x_1195_,
            v___x_1196_,
            v___y_1203_,
            v___y_1204_,
            v___y_1205_,
            v___y_1206_,
        );
        crate::leanh::lean_dec_ref(v___x_1245_);
        return v___x_1246_;
    } else {
        crate::leanh::lean_dec_ref(v___x_1201_);
        crate::leanh::lean_dec_ref(v_h_1200_);
        crate::leanh::lean_dec_ref(v_g_1199_);
        crate::leanh::lean_dec_ref(v_f_1198_);
        crate::leanh::lean_dec(v___x_1197_);
        crate::leanh::lean_dec_ref(v_a_1190_);
        crate::leanh::lean_dec_ref(v_a_1189_);
        crate::leanh::lean_dec(v_a_1185_);
        crate::leanh::lean_dec_ref(v___x_1184_);
        return v___x_1226_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_1248_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_1249_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_xs_1250_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_1251_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_1252_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_1253_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_1254_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_1255_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_00_u03b2_1256_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_1257_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_1258_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_1259_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_1260_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_f_1261_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_g_1262_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_h_1263_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_1264_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_f_x27_1265_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_1266_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_1267_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_1268_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_1269_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_1270_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_1958__boxed_1271_: u8 = 0;
    let mut v___x_1959__boxed_1272_: u8 = 0;
    let mut v___x_1960__boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958__boxed_1271_ = (crate::leanh::lean_unbox(v___x_1257_) as u8);
    v___x_1959__boxed_1272_ = (crate::leanh::lean_unbox(v___x_1258_) as u8);
    v___x_1960__boxed_1273_ = (crate::leanh::lean_unbox(v___x_1259_) as u8);
    v_res_1274_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(
        v___x_1247_,
        v_a_1248_,
        v___x_1249_,
        v_xs_1250_,
        v___x_1251_,
        v_a_1252_,
        v_a_1253_,
        v___x_1254_,
        v___x_1255_,
        v_00_u03b2_1256_,
        v___x_1958__boxed_1271_,
        v___x_1959__boxed_1272_,
        v___x_1960__boxed_1273_,
        v___x_1260_,
        v_f_1261_,
        v_g_1262_,
        v_h_1263_,
        v___x_1264_,
        v_f_x27_1265_,
        v___y_1266_,
        v___y_1267_,
        v___y_1268_,
        v___y_1269_,
    );
    crate::leanh::lean_dec(v___y_1269_);
    crate::leanh::lean_dec_ref(v___y_1268_);
    crate::leanh::lean_dec(v___y_1267_);
    crate::leanh::lean_dec_ref(v___y_1266_);
    crate::leanh::lean_dec_ref(v_xs_1250_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(
    mut v_k_1275_: *mut crate::leanh::LeanObject,
    mut v_b_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1280_);
    crate::leanh::lean_inc_ref(v___y_1279_);
    crate::leanh::lean_inc(v___y_1278_);
    crate::leanh::lean_inc_ref(v___y_1277_);
    v___x_1282_ = crate::leanh::lean_apply_6(
        v_k_1275_,
        v_b_1276_,
        v___y_1277_,
        v___y_1278_,
        v___y_1279_,
        v___y_1280_,
        crate::leanh::lean_box(0),
    );
    return v___x_1282_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_1283_: *mut crate::leanh::LeanObject,
    mut v_b_1284_: *mut crate::leanh::LeanObject,
    mut v___y_1285_: *mut crate::leanh::LeanObject,
    mut v___y_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(v_k_1283_, v_b_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
    crate::leanh::lean_dec(v___y_1288_);
    crate::leanh::lean_dec_ref(v___y_1287_);
    crate::leanh::lean_dec(v___y_1286_);
    crate::leanh::lean_dec_ref(v___y_1285_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(
    mut v_name_1291_: *mut crate::leanh::LeanObject,
    mut v_bi_1292_: u8,
    mut v_type_1293_: *mut crate::leanh::LeanObject,
    mut v_k_1294_: *mut crate::leanh::LeanObject,
    mut v_kind_1295_: u8,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1306_: u8 = 0;
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1301_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_1301_, 0, v_k_1294_);
                v___x_1302_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_1291_,
                    v_bi_1292_,
                    v_type_1293_,
                    v___f_1301_,
                    v_kind_1295_,
                    v___y_1296_,
                    v___y_1297_,
                    v___y_1298_,
                    v___y_1299_,
                );
                if crate::leanh::lean_obj_tag(v___x_1302_) == 0 {
                    v_a_1303_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
                    v_isSharedCheck_1310_ = (!crate::leanh::lean_is_exclusive(v___x_1302_)) as u8;
                    if v_isSharedCheck_1310_ == 0 {
                        v___x_1305_ = v___x_1302_;
                        v_isShared_1306_ = v_isSharedCheck_1310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1303_);
                        crate::leanh::lean_dec(v___x_1302_);
                        v___x_1305_ = crate::leanh::lean_box(0);
                        v_isShared_1306_ = v_isSharedCheck_1310_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
                    v_isSharedCheck_1318_ = (!crate::leanh::lean_is_exclusive(v___x_1302_)) as u8;
                    if v_isSharedCheck_1318_ == 0 {
                        v___x_1313_ = v___x_1302_;
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1311_);
                        crate::leanh::lean_dec(v___x_1302_);
                        v___x_1313_ = crate::leanh::lean_box(0);
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1306_ == 0 {
                    v___x_1308_ = v___x_1305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
                    v___x_1308_ = v_reuseFailAlloc_1309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1308_;
            }
            3 => {
                if v_isShared_1314_ == 0 {
                    v___x_1316_ = v___x_1313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
                    v___x_1316_ = v_reuseFailAlloc_1317_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___boxed(
    mut v_name_1319_: *mut crate::leanh::LeanObject,
    mut v_bi_1320_: *mut crate::leanh::LeanObject,
    mut v_type_1321_: *mut crate::leanh::LeanObject,
    mut v_k_1322_: *mut crate::leanh::LeanObject,
    mut v_kind_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1329_: u8 = 0;
    let mut v_kind_boxed_1330_: u8 = 0;
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1329_ = (crate::leanh::lean_unbox(v_bi_1320_) as u8);
    v_kind_boxed_1330_ = (crate::leanh::lean_unbox(v_kind_1323_) as u8);
    v_res_1331_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_1319_, v_bi_boxed_1329_, v_type_1321_, v_k_1322_, v_kind_boxed_1330_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
    crate::leanh::lean_dec(v___y_1327_);
    crate::leanh::lean_dec_ref(v___y_1326_);
    crate::leanh::lean_dec(v___y_1325_);
    crate::leanh::lean_dec_ref(v___y_1324_);
    return v_res_1331_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(
    mut v_name_1332_: *mut crate::leanh::LeanObject,
    mut v_type_1333_: *mut crate::leanh::LeanObject,
    mut v_k_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1340_: u8 = 0;
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = 0;
    v___x_1341_ = 0;
    v___x_1342_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_1332_, v___x_1340_, v_type_1333_, v_k_1334_, v___x_1341_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
    return v___x_1342_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg___boxed(
    mut v_name_1343_: *mut crate::leanh::LeanObject,
    mut v_type_1344_: *mut crate::leanh::LeanObject,
    mut v_k_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1351_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_1343_, v_type_1344_, v_k_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
    crate::leanh::lean_dec(v___y_1349_);
    crate::leanh::lean_dec_ref(v___y_1348_);
    crate::leanh::lean_dec(v___y_1347_);
    crate::leanh::lean_dec_ref(v___y_1346_);
    return v_res_1351_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(
    mut v_xs_1358_: *mut crate::leanh::LeanObject,
    mut v___x_1359_: *mut crate::leanh::LeanObject,
    mut v___x_1360_: u8,
    mut v___x_1361_: u8,
    mut v___x_1362_: u8,
    mut v_f_1363_: *mut crate::leanh::LeanObject,
    mut v_g_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v___x_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v___x_1368_: *mut crate::leanh::LeanObject,
    mut v___x_1369_: *mut crate::leanh::LeanObject,
    mut v___x_1370_: *mut crate::leanh::LeanObject,
    mut v___x_1371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_h_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = l_Lean_Meta_mkForallFVars(
        v_xs_1358_,
        v___x_1359_,
        v___x_1360_,
        v___x_1361_,
        v___x_1361_,
        v___x_1362_,
        v___y_1374_,
        v___y_1375_,
        v___y_1376_,
        v___y_1377_,
    );
    if crate::leanh::lean_obj_tag(v___x_1379_) == 0 {
        let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
        crate::leanh::lean_inc(v_a_1380_);
        crate::leanh::lean_dec_ref_known(v___x_1379_, 1);
        v___x_1381_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1382_ = lean_mk_empty_array_with_capacity(v___x_1381_);
        crate::leanh::lean_inc_ref(v_f_1363_);
        v___x_1383_ = lean_array_push(v___x_1382_, v_f_1363_);
        crate::leanh::lean_inc_ref(v_g_1364_);
        v___x_1384_ = lean_array_push(v___x_1383_, v_g_1364_);
        v___x_1385_ = l_Lean_Meta_mkLambdaFVars(
            v___x_1384_,
            v_a_1380_,
            v___x_1360_,
            v___x_1361_,
            v___x_1360_,
            v___x_1361_,
            v___x_1362_,
            v___y_1374_,
            v___y_1375_,
            v___y_1376_,
            v___y_1377_,
        );
        crate::leanh::lean_dec_ref(v___x_1384_);
        if crate::leanh::lean_obj_tag(v___x_1385_) == 0 {
            let mut v_a_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1386_ = crate::leanh::lean_ctor_get(v___x_1385_, 0);
            crate::leanh::lean_inc_n(v_a_1386_, 2);
            crate::leanh::lean_dec_ref_known(v___x_1385_, 1);
            v___x_1387_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0;
            v___x_1388_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1;
            crate::leanh::lean_inc(v_a_1365_);
            v___x_1389_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1389_, 0, v_a_1365_);
            crate::leanh::lean_ctor_set(v___x_1389_, 1, v___x_1366_);
            crate::leanh::lean_inc_ref(v___x_1389_);
            v___x_1390_ = l_Lean_mkConst(v___x_1388_, v___x_1389_);
            crate::leanh::lean_inc_ref(v_a_1367_);
            v___x_1391_ = l_Lean_mkAppB(v___x_1390_, v_a_1367_, v_a_1386_);
            v___x_1392_ = crate::leanh::lean_box((v___x_1360_) as usize);
            v___x_1393_ = crate::leanh::lean_box((v___x_1361_) as usize);
            v___x_1394_ = crate::leanh::lean_box((v___x_1362_) as usize);
            crate::leanh::lean_inc_ref(v___x_1391_);
            v___f_1395_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed as *mut core::ffi::c_void, 24, 18);
            crate::leanh::lean_closure_set(v___f_1395_, 0, v___x_1387_);
            crate::leanh::lean_closure_set(v___f_1395_, 1, v_a_1365_);
            crate::leanh::lean_closure_set(v___f_1395_, 2, v___x_1368_);
            crate::leanh::lean_closure_set(v___f_1395_, 3, v_xs_1358_);
            crate::leanh::lean_closure_set(v___f_1395_, 4, v___x_1369_);
            crate::leanh::lean_closure_set(v___f_1395_, 5, v_a_1367_);
            crate::leanh::lean_closure_set(v___f_1395_, 6, v_a_1386_);
            crate::leanh::lean_closure_set(v___f_1395_, 7, v___x_1370_);
            crate::leanh::lean_closure_set(v___f_1395_, 8, v___x_1371_);
            crate::leanh::lean_closure_set(v___f_1395_, 9, v_00_u03b2_1372_);
            crate::leanh::lean_closure_set(v___f_1395_, 10, v___x_1392_);
            crate::leanh::lean_closure_set(v___f_1395_, 11, v___x_1393_);
            crate::leanh::lean_closure_set(v___f_1395_, 12, v___x_1394_);
            crate::leanh::lean_closure_set(v___f_1395_, 13, v___x_1389_);
            crate::leanh::lean_closure_set(v___f_1395_, 14, v_f_1363_);
            crate::leanh::lean_closure_set(v___f_1395_, 15, v_g_1364_);
            crate::leanh::lean_closure_set(v___f_1395_, 16, v_h_1373_);
            crate::leanh::lean_closure_set(v___f_1395_, 17, v___x_1391_);
            v___x_1396_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3;
            v___x_1397_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_1396_, v___x_1391_, v___f_1395_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
            return v___x_1397_;
        } else {
            crate::leanh::lean_dec_ref(v_h_1373_);
            crate::leanh::lean_dec_ref(v_00_u03b2_1372_);
            crate::leanh::lean_dec(v___x_1371_);
            crate::leanh::lean_dec(v___x_1370_);
            crate::leanh::lean_dec(v___x_1369_);
            crate::leanh::lean_dec(v___x_1368_);
            crate::leanh::lean_dec_ref(v_a_1367_);
            crate::leanh::lean_dec(v___x_1366_);
            crate::leanh::lean_dec(v_a_1365_);
            crate::leanh::lean_dec_ref(v_g_1364_);
            crate::leanh::lean_dec_ref(v_f_1363_);
            crate::leanh::lean_dec_ref(v_xs_1358_);
            return v___x_1385_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_h_1373_);
        crate::leanh::lean_dec_ref(v_00_u03b2_1372_);
        crate::leanh::lean_dec(v___x_1371_);
        crate::leanh::lean_dec(v___x_1370_);
        crate::leanh::lean_dec(v___x_1369_);
        crate::leanh::lean_dec(v___x_1368_);
        crate::leanh::lean_dec_ref(v_a_1367_);
        crate::leanh::lean_dec(v___x_1366_);
        crate::leanh::lean_dec(v_a_1365_);
        crate::leanh::lean_dec_ref(v_g_1364_);
        crate::leanh::lean_dec_ref(v_f_1363_);
        crate::leanh::lean_dec_ref(v_xs_1358_);
        return v___x_1379_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_xs_1398_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_1399_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_1400_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1401_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_1402_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_f_1403_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_g_1404_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_1405_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_1406_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_1407_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_1408_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_1409_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_1410_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_1411_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_00_u03b2_1412_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_h_1413_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1414_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_1415_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_1416_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_1417_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_1418_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_2195__boxed_1419_: u8 = 0;
    let mut v___x_2196__boxed_1420_: u8 = 0;
    let mut v___x_2197__boxed_1421_: u8 = 0;
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195__boxed_1419_ = (crate::leanh::lean_unbox(v___x_1400_) as u8);
    v___x_2196__boxed_1420_ = (crate::leanh::lean_unbox(v___x_1401_) as u8);
    v___x_2197__boxed_1421_ = (crate::leanh::lean_unbox(v___x_1402_) as u8);
    v_res_1422_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(
        v_xs_1398_,
        v___x_1399_,
        v___x_2195__boxed_1419_,
        v___x_2196__boxed_1420_,
        v___x_2197__boxed_1421_,
        v_f_1403_,
        v_g_1404_,
        v_a_1405_,
        v___x_1406_,
        v_a_1407_,
        v___x_1408_,
        v___x_1409_,
        v___x_1410_,
        v___x_1411_,
        v_00_u03b2_1412_,
        v_h_1413_,
        v___y_1414_,
        v___y_1415_,
        v___y_1416_,
        v___y_1417_,
    );
    crate::leanh::lean_dec(v___y_1417_);
    crate::leanh::lean_dec_ref(v___y_1416_);
    crate::leanh::lean_dec(v___y_1415_);
    crate::leanh::lean_dec_ref(v___y_1414_);
    return v_res_1422_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_f_1430_: *mut crate::leanh::LeanObject,
    mut v_xs_1431_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1432_: *mut crate::leanh::LeanObject,
    mut v___x_1433_: u8,
    mut v___x_1434_: u8,
    mut v___x_1435_: u8,
    mut v_a_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v___x_1438_: *mut crate::leanh::LeanObject,
    mut v___x_1439_: *mut crate::leanh::LeanObject,
    mut v_g_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1;
    v___x_1447_ = crate::leanh::lean_box(0);
    v___x_1448_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1448_, 0, v_a_1429_);
    crate::leanh::lean_ctor_set(v___x_1448_, 1, v___x_1447_);
    crate::leanh::lean_inc_ref(v___x_1448_);
    v___x_1449_ = l_Lean_mkConst(v___x_1446_, v___x_1448_);
    crate::leanh::lean_inc_ref(v_f_1430_);
    v___x_1450_ = l_Lean_mkAppN(v_f_1430_, v_xs_1431_);
    crate::leanh::lean_inc_ref(v_g_1440_);
    v___x_1451_ = l_Lean_mkAppN(v_g_1440_, v_xs_1431_);
    crate::leanh::lean_inc_ref(v_00_u03b2_1432_);
    v___x_1452_ = l_Lean_mkApp3(v___x_1449_, v_00_u03b2_1432_, v___x_1450_, v___x_1451_);
    crate::leanh::lean_inc_ref(v___x_1452_);
    v___x_1453_ = l_Lean_Meta_mkForallFVars(
        v_xs_1431_,
        v___x_1452_,
        v___x_1433_,
        v___x_1434_,
        v___x_1434_,
        v___x_1435_,
        v___y_1441_,
        v___y_1442_,
        v___y_1443_,
        v___y_1444_,
    );
    if crate::leanh::lean_obj_tag(v___x_1453_) == 0 {
        let mut v_a_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1454_ = crate::leanh::lean_ctor_get(v___x_1453_, 0);
        crate::leanh::lean_inc(v_a_1454_);
        crate::leanh::lean_dec_ref_known(v___x_1453_, 1);
        v___x_1455_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3;
        v___x_1456_ = crate::leanh::lean_box((v___x_1433_) as usize);
        v___x_1457_ = crate::leanh::lean_box((v___x_1434_) as usize);
        v___x_1458_ = crate::leanh::lean_box((v___x_1435_) as usize);
        v___f_1459_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed
                as *mut core::ffi::c_void,
            21,
            15,
        );
        crate::leanh::lean_closure_set(v___f_1459_, 0, v_xs_1431_);
        crate::leanh::lean_closure_set(v___f_1459_, 1, v___x_1452_);
        crate::leanh::lean_closure_set(v___f_1459_, 2, v___x_1456_);
        crate::leanh::lean_closure_set(v___f_1459_, 3, v___x_1457_);
        crate::leanh::lean_closure_set(v___f_1459_, 4, v___x_1458_);
        crate::leanh::lean_closure_set(v___f_1459_, 5, v_f_1430_);
        crate::leanh::lean_closure_set(v___f_1459_, 6, v_g_1440_);
        crate::leanh::lean_closure_set(v___f_1459_, 7, v_a_1436_);
        crate::leanh::lean_closure_set(v___f_1459_, 8, v___x_1447_);
        crate::leanh::lean_closure_set(v___f_1459_, 9, v_a_1437_);
        crate::leanh::lean_closure_set(v___f_1459_, 10, v___x_1448_);
        crate::leanh::lean_closure_set(v___f_1459_, 11, v___x_1438_);
        crate::leanh::lean_closure_set(v___f_1459_, 12, v___x_1455_);
        crate::leanh::lean_closure_set(v___f_1459_, 13, v___x_1439_);
        crate::leanh::lean_closure_set(v___f_1459_, 14, v_00_u03b2_1432_);
        v___x_1460_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_1455_, v_a_1454_, v___f_1459_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
        return v___x_1460_;
    } else {
        crate::leanh::lean_dec_ref(v___x_1452_);
        crate::leanh::lean_dec_ref_known(v___x_1448_, 2);
        crate::leanh::lean_dec_ref(v_g_1440_);
        crate::leanh::lean_dec(v___x_1439_);
        crate::leanh::lean_dec(v___x_1438_);
        crate::leanh::lean_dec_ref(v_a_1437_);
        crate::leanh::lean_dec(v_a_1436_);
        crate::leanh::lean_dec_ref(v_00_u03b2_1432_);
        crate::leanh::lean_dec_ref(v_xs_1431_);
        crate::leanh::lean_dec_ref(v_f_1430_);
        return v___x_1453_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1461_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_f_1462_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_xs_1463_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_1464_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_1465_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_1466_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_1467_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_1468_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_1469_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_1470_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_1471_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_g_1472_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1473_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1474_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1475_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1476_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1477_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_2301__boxed_1478_: u8 = 0;
    let mut v___x_2302__boxed_1479_: u8 = 0;
    let mut v___x_2303__boxed_1480_: u8 = 0;
    let mut v_res_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301__boxed_1478_ = (crate::leanh::lean_unbox(v___x_1465_) as u8);
    v___x_2302__boxed_1479_ = (crate::leanh::lean_unbox(v___x_1466_) as u8);
    v___x_2303__boxed_1480_ = (crate::leanh::lean_unbox(v___x_1467_) as u8);
    v_res_1481_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(
        v_a_1461_,
        v_f_1462_,
        v_xs_1463_,
        v_00_u03b2_1464_,
        v___x_2301__boxed_1478_,
        v___x_2302__boxed_1479_,
        v___x_2303__boxed_1480_,
        v_a_1468_,
        v_a_1469_,
        v___x_1470_,
        v___x_1471_,
        v_g_1472_,
        v___y_1473_,
        v___y_1474_,
        v___y_1475_,
        v___y_1476_,
    );
    crate::leanh::lean_dec(v___y_1476_);
    crate::leanh::lean_dec_ref(v___y_1475_);
    crate::leanh::lean_dec(v___y_1474_);
    crate::leanh::lean_dec_ref(v___y_1473_);
    return v_res_1481_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_xs_1486_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1487_: *mut crate::leanh::LeanObject,
    mut v___x_1488_: u8,
    mut v___x_1489_: u8,
    mut v___x_1490_: u8,
    mut v_a_1491_: *mut crate::leanh::LeanObject,
    mut v_a_1492_: *mut crate::leanh::LeanObject,
    mut v___x_1493_: *mut crate::leanh::LeanObject,
    mut v_f_1494_: *mut crate::leanh::LeanObject,
    mut v___y_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1;
    v___x_1501_ = crate::leanh::lean_box((v___x_1488_) as usize);
    v___x_1502_ = crate::leanh::lean_box((v___x_1489_) as usize);
    v___x_1503_ = crate::leanh::lean_box((v___x_1490_) as usize);
    crate::leanh::lean_inc_ref(v_a_1492_);
    v___f_1504_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed
            as *mut core::ffi::c_void,
        17,
        11,
    );
    crate::leanh::lean_closure_set(v___f_1504_, 0, v_a_1485_);
    crate::leanh::lean_closure_set(v___f_1504_, 1, v_f_1494_);
    crate::leanh::lean_closure_set(v___f_1504_, 2, v_xs_1486_);
    crate::leanh::lean_closure_set(v___f_1504_, 3, v_00_u03b2_1487_);
    crate::leanh::lean_closure_set(v___f_1504_, 4, v___x_1501_);
    crate::leanh::lean_closure_set(v___f_1504_, 5, v___x_1502_);
    crate::leanh::lean_closure_set(v___f_1504_, 6, v___x_1503_);
    crate::leanh::lean_closure_set(v___f_1504_, 7, v_a_1491_);
    crate::leanh::lean_closure_set(v___f_1504_, 8, v_a_1492_);
    crate::leanh::lean_closure_set(v___f_1504_, 9, v___x_1493_);
    crate::leanh::lean_closure_set(v___f_1504_, 10, v___x_1500_);
    v___x_1505_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_1500_, v_a_1492_, v___f_1504_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
    return v___x_1505_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed(
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_xs_1507_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1508_: *mut crate::leanh::LeanObject,
    mut v___x_1509_: *mut crate::leanh::LeanObject,
    mut v___x_1510_: *mut crate::leanh::LeanObject,
    mut v___x_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v___x_1514_: *mut crate::leanh::LeanObject,
    mut v_f_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2383__boxed_1521_: u8 = 0;
    let mut v___x_2384__boxed_1522_: u8 = 0;
    let mut v___x_2385__boxed_1523_: u8 = 0;
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2383__boxed_1521_ = (crate::leanh::lean_unbox(v___x_1509_) as u8);
    v___x_2384__boxed_1522_ = (crate::leanh::lean_unbox(v___x_1510_) as u8);
    v___x_2385__boxed_1523_ = (crate::leanh::lean_unbox(v___x_1511_) as u8);
    v_res_1524_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(
        v_a_1506_,
        v_xs_1507_,
        v_00_u03b2_1508_,
        v___x_2383__boxed_1521_,
        v___x_2384__boxed_1522_,
        v___x_2385__boxed_1523_,
        v_a_1512_,
        v_a_1513_,
        v___x_1514_,
        v_f_1515_,
        v___y_1516_,
        v___y_1517_,
        v___y_1518_,
        v___y_1519_,
    );
    crate::leanh::lean_dec(v___y_1519_);
    crate::leanh::lean_dec_ref(v___y_1518_);
    crate::leanh::lean_dec(v___y_1517_);
    crate::leanh::lean_dec_ref(v___y_1516_);
    return v_res_1524_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(
    mut v_xs_1528_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_a_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1535_ = 0;
                v___x_1536_ = 1;
                v___x_1537_ = 1;
                crate::leanh::lean_inc_ref(v_00_u03b2_1529_);
                v___x_1538_ = l_Lean_Meta_mkForallFVars(
                    v_xs_1528_,
                    v_00_u03b2_1529_,
                    v___x_1535_,
                    v___x_1536_,
                    v___x_1536_,
                    v___x_1537_,
                    v_a_1530_,
                    v_a_1531_,
                    v_a_1532_,
                    v_a_1533_,
                );
                if crate::leanh::lean_obj_tag(v___x_1538_) == 0 {
                    v_a_1539_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    crate::leanh::lean_inc(v_a_1539_);
                    crate::leanh::lean_dec_ref_known(v___x_1538_, 1);
                    crate::leanh::lean_inc_ref(v_00_u03b2_1529_);
                    v___x_1540_ = l_Lean_Meta_getLevel(
                        v_00_u03b2_1529_,
                        v_a_1530_,
                        v_a_1531_,
                        v_a_1532_,
                        v_a_1533_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1540_) == 0 {
                        v_a_1541_ = crate::leanh::lean_ctor_get(v___x_1540_, 0);
                        crate::leanh::lean_inc(v_a_1541_);
                        crate::leanh::lean_dec_ref_known(v___x_1540_, 1);
                        crate::leanh::lean_inc(v_a_1539_);
                        v___x_1542_ = l_Lean_Meta_getLevel(
                            v_a_1539_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1542_) == 0 {
                            v_a_1543_ = crate::leanh::lean_ctor_get(v___x_1542_, 0);
                            crate::leanh::lean_inc(v_a_1543_);
                            crate::leanh::lean_dec_ref_known(v___x_1542_, 1);
                            v___x_1544_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1;
                            v___x_1545_ = crate::leanh::lean_box((v___x_1535_) as usize);
                            v___x_1546_ = crate::leanh::lean_box((v___x_1536_) as usize);
                            v___x_1547_ = crate::leanh::lean_box((v___x_1537_) as usize);
                            crate::leanh::lean_inc(v_a_1539_);
                            v___f_1548_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed as *mut core::ffi::c_void, 15, 9);
                            crate::leanh::lean_closure_set(v___f_1548_, 0, v_a_1541_);
                            crate::leanh::lean_closure_set(v___f_1548_, 1, v_xs_1528_);
                            crate::leanh::lean_closure_set(v___f_1548_, 2, v_00_u03b2_1529_);
                            crate::leanh::lean_closure_set(v___f_1548_, 3, v___x_1545_);
                            crate::leanh::lean_closure_set(v___f_1548_, 4, v___x_1546_);
                            crate::leanh::lean_closure_set(v___f_1548_, 5, v___x_1547_);
                            crate::leanh::lean_closure_set(v___f_1548_, 6, v_a_1543_);
                            crate::leanh::lean_closure_set(v___f_1548_, 7, v_a_1539_);
                            crate::leanh::lean_closure_set(v___f_1548_, 8, v___x_1544_);
                            v___x_1549_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_1544_, v_a_1539_, v___f_1548_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
                            return v___x_1549_;
                        } else {
                            crate::leanh::lean_dec(v_a_1541_);
                            crate::leanh::lean_dec(v_a_1539_);
                            crate::leanh::lean_dec_ref(v_00_u03b2_1529_);
                            crate::leanh::lean_dec_ref(v_xs_1528_);
                            v_a_1550_ = crate::leanh::lean_ctor_get(v___x_1542_, 0);
                            v_isSharedCheck_1557_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1542_)) as u8;
                            if v_isSharedCheck_1557_ == 0 {
                                v___x_1552_ = v___x_1542_;
                                v_isShared_1553_ = v_isSharedCheck_1557_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1550_);
                                crate::leanh::lean_dec(v___x_1542_);
                                v___x_1552_ = crate::leanh::lean_box(0);
                                v_isShared_1553_ = v_isSharedCheck_1557_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1539_);
                        crate::leanh::lean_dec_ref(v_00_u03b2_1529_);
                        crate::leanh::lean_dec_ref(v_xs_1528_);
                        v_a_1558_ = crate::leanh::lean_ctor_get(v___x_1540_, 0);
                        v_isSharedCheck_1565_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1540_)) as u8;
                        if v_isSharedCheck_1565_ == 0 {
                            v___x_1560_ = v___x_1540_;
                            v_isShared_1561_ = v_isSharedCheck_1565_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1558_);
                            crate::leanh::lean_dec(v___x_1540_);
                            v___x_1560_ = crate::leanh::lean_box(0);
                            v_isShared_1561_ = v_isSharedCheck_1565_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03b2_1529_);
                    crate::leanh::lean_dec_ref(v_xs_1528_);
                    return v___x_1538_;
                }
            }
            1 => {
                if v_isShared_1553_ == 0 {
                    v___x_1555_ = v___x_1552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
                    v___x_1555_ = v_reuseFailAlloc_1556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1555_;
            }
            3 => {
                if v_isShared_1561_ == 0 {
                    v___x_1563_ = v___x_1560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___boxed(
    mut v_xs_1566_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1573_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(
        v_xs_1566_,
        v_00_u03b2_1567_,
        v_a_1568_,
        v_a_1569_,
        v_a_1570_,
        v_a_1571_,
    );
    crate::leanh::lean_dec(v_a_1571_);
    crate::leanh::lean_dec_ref(v_a_1570_);
    crate::leanh::lean_dec(v_a_1569_);
    crate::leanh::lean_dec_ref(v_a_1568_);
    return v_res_1573_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(
    mut v_00_u03b1_1574_: *mut crate::leanh::LeanObject,
    mut v_name_1575_: *mut crate::leanh::LeanObject,
    mut v_bi_1576_: u8,
    mut v_type_1577_: *mut crate::leanh::LeanObject,
    mut v_k_1578_: *mut crate::leanh::LeanObject,
    mut v_kind_1579_: u8,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_1575_, v_bi_1576_, v_type_1577_, v_k_1578_, v_kind_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
    return v___x_1585_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___boxed(
    mut v_00_u03b1_1586_: *mut crate::leanh::LeanObject,
    mut v_name_1587_: *mut crate::leanh::LeanObject,
    mut v_bi_1588_: *mut crate::leanh::LeanObject,
    mut v_type_1589_: *mut crate::leanh::LeanObject,
    mut v_k_1590_: *mut crate::leanh::LeanObject,
    mut v_kind_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1597_: u8 = 0;
    let mut v_kind_boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1597_ = (crate::leanh::lean_unbox(v_bi_1588_) as u8);
    v_kind_boxed_1598_ = (crate::leanh::lean_unbox(v_kind_1591_) as u8);
    v_res_1599_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(v_00_u03b1_1586_, v_name_1587_, v_bi_boxed_1597_, v_type_1589_, v_k_1590_, v_kind_boxed_1598_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
    crate::leanh::lean_dec(v___y_1595_);
    crate::leanh::lean_dec_ref(v___y_1594_);
    crate::leanh::lean_dec(v___y_1593_);
    crate::leanh::lean_dec_ref(v___y_1592_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(
    mut v_00_u03b1_1600_: *mut crate::leanh::LeanObject,
    mut v_name_1601_: *mut crate::leanh::LeanObject,
    mut v_type_1602_: *mut crate::leanh::LeanObject,
    mut v_k_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_1601_, v_type_1602_, v_k_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___boxed(
    mut v_00_u03b1_1610_: *mut crate::leanh::LeanObject,
    mut v_name_1611_: *mut crate::leanh::LeanObject,
    mut v_type_1612_: *mut crate::leanh::LeanObject,
    mut v_k_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(v_00_u03b1_1610_, v_name_1611_, v_type_1612_, v_k_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
    crate::leanh::lean_dec(v___y_1617_);
    crate::leanh::lean_dec_ref(v___y_1616_);
    crate::leanh::lean_dec(v___y_1615_);
    crate::leanh::lean_dec_ref(v___y_1614_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1620_: *mut crate::leanh::LeanObject,
    mut v_vals_1621_: *mut crate::leanh::LeanObject,
    mut v_i_1622_: *mut crate::leanh::LeanObject,
    mut v_k_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1624_ = lean_array_get_size(v_keys_1620_);
                v___x_1625_ = lean_nat_dec_lt(v_i_1622_, v___x_1624_);
                if v___x_1625_ == 0 {
                    crate::leanh::lean_dec(v_i_1622_);
                    v___x_1626_ = crate::leanh::lean_box(0);
                    return v___x_1626_;
                } else {
                    v_k_x27_1627_ = lean_array_fget_borrowed(v_keys_1620_, v_i_1622_);
                    v___x_1628_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1623_,
                            v_k_x27_1627_,
                        );
                    if v___x_1628_ == 0 {
                        v___x_1629_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1630_ = lean_nat_add(v_i_1622_, v___x_1629_);
                        crate::leanh::lean_dec(v_i_1622_);
                        v_i_1622_ = v___x_1630_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1632_ = lean_array_fget_borrowed(v_vals_1621_, v_i_1622_);
                        crate::leanh::lean_dec(v_i_1622_);
                        crate::leanh::lean_inc(v___x_1632_);
                        v___x_1633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1633_, 0, v___x_1632_);
                        return v___x_1633_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1634_: *mut crate::leanh::LeanObject,
    mut v_vals_1635_: *mut crate::leanh::LeanObject,
    mut v_i_1636_: *mut crate::leanh::LeanObject,
    mut v_k_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_1634_, v_vals_1635_, v_i_1636_, v_k_1637_);
    crate::leanh::lean_dec_ref(v_k_1637_);
    crate::leanh::lean_dec_ref(v_vals_1635_);
    crate::leanh::lean_dec_ref(v_keys_1634_);
    return v_res_1638_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1639_: usize = 0;
    let mut v___x_1640_: usize = 0;
    let mut v___x_1641_: usize = 0;
    v___x_1639_ = 5usize;
    v___x_1640_ = 1usize;
    v___x_1641_ = lean_usize_shift_left(v___x_1640_, v___x_1639_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: usize = 0;
    v___x_1642_ = 1usize;
    v___x_1643_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0);
    v___x_1644_ = lean_usize_sub(v___x_1643_, v___x_1642_);
    return v___x_1644_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(
    mut v_x_1645_: *mut crate::leanh::LeanObject,
    mut v_x_1646_: usize,
    mut v_x_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: usize = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: usize = 0;
    let mut v_j_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: usize = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1645_) == 0 {
                    v_es_1648_ = crate::leanh::lean_ctor_get(v_x_1645_, 0);
                    v___x_1649_ = crate::leanh::lean_box(2);
                    v___x_1650_ = 5usize;
                    v___x_1651_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1);
                    v___x_1652_ = lean_usize_land(v_x_1646_, v___x_1651_);
                    v_j_1653_ = lean_usize_to_nat(v___x_1652_);
                    v___x_1654_ = lean_array_get_borrowed(v___x_1649_, v_es_1648_, v_j_1653_);
                    crate::leanh::lean_dec(v_j_1653_);
                    match crate::leanh::lean_obj_tag(v___x_1654_) {
                        0 => {
                            v_key_1655_ = crate::leanh::lean_ctor_get(v___x_1654_, 0);
                            v_val_1656_ = crate::leanh::lean_ctor_get(v___x_1654_, 1);
                            v___x_1657_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1647_, v_key_1655_);
                            if v___x_1657_ == 0 {
                                v___x_1658_ = crate::leanh::lean_box(0);
                                return v___x_1658_;
                            } else {
                                crate::leanh::lean_inc(v_val_1656_);
                                v___x_1659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1659_, 0, v_val_1656_);
                                return v___x_1659_;
                            }
                        }
                        1 => {
                            v_node_1660_ = crate::leanh::lean_ctor_get(v___x_1654_, 0);
                            v___x_1661_ = lean_usize_shift_right(v_x_1646_, v___x_1650_);
                            v_x_1645_ = v_node_1660_;
                            v_x_1646_ = v___x_1661_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1663_ = crate::leanh::lean_box(0);
                            return v___x_1663_;
                        }
                    }
                } else {
                    v_ks_1664_ = crate::leanh::lean_ctor_get(v_x_1645_, 0);
                    v_vs_1665_ = crate::leanh::lean_ctor_get(v_x_1645_, 1);
                    v___x_1666_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1667_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_ks_1664_, v_vs_1665_, v___x_1666_, v_x_1647_);
                    return v___x_1667_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(
    mut v_x_1668_: *mut crate::leanh::LeanObject,
    mut v_x_1669_: *mut crate::leanh::LeanObject,
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6888__boxed_1671_: usize = 0;
    let mut v_res_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6888__boxed_1671_ = crate::leanh::lean_unbox_usize(v_x_1669_);
    crate::leanh::lean_dec(v_x_1669_);
    v_res_1672_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_1668_, v_x_6888__boxed_1671_, v_x_1670_);
    crate::leanh::lean_dec_ref(v_x_1670_);
    crate::leanh::lean_dec_ref(v_x_1668_);
    return v_res_1672_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(
    mut v_x_1673_: *mut crate::leanh::LeanObject,
    mut v_x_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1675_: u64 = 0;
    let mut v___x_1676_: usize = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1675_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1674_);
    v___x_1676_ = lean_uint64_to_usize(v___x_1675_);
    v___x_1677_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_1673_, v___x_1676_, v_x_1674_);
    return v___x_1677_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(
    mut v_x_1678_: *mut crate::leanh::LeanObject,
    mut v_x_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1680_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_1678_, v_x_1679_);
    crate::leanh::lean_dec_ref(v_x_1679_);
    crate::leanh::lean_dec_ref(v_x_1678_);
    return v_res_1680_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_1681_: *mut crate::leanh::LeanObject,
    mut v_x_1682_: *mut crate::leanh::LeanObject,
    mut v_x_1683_: *mut crate::leanh::LeanObject,
    mut v_x_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1685_ = crate::leanh::lean_ctor_get(v_x_1681_, 0);
                v_vs_1686_ = crate::leanh::lean_ctor_get(v_x_1681_, 1);
                v_isSharedCheck_1710_ = (!crate::leanh::lean_is_exclusive(v_x_1681_)) as u8;
                if v_isSharedCheck_1710_ == 0 {
                    v___x_1688_ = v_x_1681_;
                    v_isShared_1689_ = v_isSharedCheck_1710_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1686_);
                    crate::leanh::lean_inc(v_ks_1685_);
                    crate::leanh::lean_dec(v_x_1681_);
                    v___x_1688_ = crate::leanh::lean_box(0);
                    v_isShared_1689_ = v_isSharedCheck_1710_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1690_ = lean_array_get_size(v_ks_1685_);
                v___x_1691_ = lean_nat_dec_lt(v_x_1682_, v___x_1690_);
                if v___x_1691_ == 0 {
                    crate::leanh::lean_dec(v_x_1682_);
                    v___x_1692_ = lean_array_push(v_ks_1685_, v_x_1683_);
                    v___x_1693_ = lean_array_push(v_vs_1686_, v_x_1684_);
                    if v_isShared_1689_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1693_);
                        crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1692_);
                        v___x_1695_ = v___x_1688_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1696_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1692_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
                        v___x_1695_ = v_reuseFailAlloc_1696_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1697_ = lean_array_fget_borrowed(v_ks_1685_, v_x_1682_);
                    v___x_1698_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1683_,
                            v_k_x27_1697_,
                        );
                    if v___x_1698_ == 0 {
                        if v_isShared_1689_ == 0 {
                            v___x_1700_ = v___x_1688_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1704_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_ks_1685_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_vs_1686_);
                            v___x_1700_ = v_reuseFailAlloc_1704_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1705_ = lean_array_fset(v_ks_1685_, v_x_1682_, v_x_1683_);
                        v___x_1706_ = lean_array_fset(v_vs_1686_, v_x_1682_, v_x_1684_);
                        crate::leanh::lean_dec(v_x_1682_);
                        if v_isShared_1689_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1706_);
                            crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1705_);
                            v___x_1708_ = v___x_1688_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1709_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1705_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
                            v___x_1708_ = v_reuseFailAlloc_1709_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1695_;
            }
            3 => {
                v___x_1701_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1702_ = lean_nat_add(v_x_1682_, v___x_1701_);
                crate::leanh::lean_dec(v_x_1682_);
                v_x_1681_ = v___x_1700_;
                v_x_1682_ = v___x_1702_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(
    mut v_n_1711_: *mut crate::leanh::LeanObject,
    mut v_k_1712_: *mut crate::leanh::LeanObject,
    mut v_v_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1715_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1711_, v___x_1714_, v_k_1712_, v_v_1713_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1716_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(
    mut v_x_1717_: *mut crate::leanh::LeanObject,
    mut v_x_1718_: usize,
    mut v_x_1719_: usize,
    mut v_x_1720_: *mut crate::leanh::LeanObject,
    mut v_x_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: usize = 0;
    let mut v___x_1726_: usize = 0;
    let mut v_j_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v_v_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1747_: u8 = 0;
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v_node_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v_unused_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: u8 = 0;
    let mut v_ks_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: usize = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v_reuseFailAlloc_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1717_) == 0 {
                    v_es_1722_ = crate::leanh::lean_ctor_get(v_x_1717_, 0);
                    v___x_1723_ = 5usize;
                    v___x_1724_ = 1usize;
                    v___x_1725_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1);
                    v___x_1726_ = lean_usize_land(v_x_1718_, v___x_1725_);
                    v_j_1727_ = lean_usize_to_nat(v___x_1726_);
                    v___x_1728_ = lean_array_get_size(v_es_1722_);
                    v___x_1729_ = lean_nat_dec_lt(v_j_1727_, v___x_1728_);
                    if v___x_1729_ == 0 {
                        crate::leanh::lean_dec(v_j_1727_);
                        crate::leanh::lean_dec(v_x_1721_);
                        crate::leanh::lean_dec_ref(v_x_1720_);
                        return v_x_1717_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1722_);
                        v_isSharedCheck_1766_ = (!crate::leanh::lean_is_exclusive(v_x_1717_)) as u8;
                        if v_isSharedCheck_1766_ == 0 {
                            v_unused_1767_ = crate::leanh::lean_ctor_get(v_x_1717_, 0);
                            crate::leanh::lean_dec(v_unused_1767_);
                            v___x_1731_ = v_x_1717_;
                            v_isShared_1732_ = v_isSharedCheck_1766_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1717_);
                            v___x_1731_ = crate::leanh::lean_box(0);
                            v_isShared_1732_ = v_isSharedCheck_1766_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1768_ = crate::leanh::lean_ctor_get(v_x_1717_, 0);
                    v_vs_1769_ = crate::leanh::lean_ctor_get(v_x_1717_, 1);
                    v_isSharedCheck_1789_ = (!crate::leanh::lean_is_exclusive(v_x_1717_)) as u8;
                    if v_isSharedCheck_1789_ == 0 {
                        v___x_1771_ = v_x_1717_;
                        v_isShared_1772_ = v_isSharedCheck_1789_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1769_);
                        crate::leanh::lean_inc(v_ks_1768_);
                        crate::leanh::lean_dec(v_x_1717_);
                        v___x_1771_ = crate::leanh::lean_box(0);
                        v_isShared_1772_ = v_isSharedCheck_1789_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1733_ = lean_array_fget(v_es_1722_, v_j_1727_);
                v___x_1734_ = crate::leanh::lean_box(0);
                v_xs_x27_1735_ = lean_array_fset(v_es_1722_, v_j_1727_, v___x_1734_);
                match crate::leanh::lean_obj_tag(v_v_1733_) {
                    0 => {
                        v_key_1742_ = crate::leanh::lean_ctor_get(v_v_1733_, 0);
                        v_val_1743_ = crate::leanh::lean_ctor_get(v_v_1733_, 1);
                        v_isSharedCheck_1753_ = (!crate::leanh::lean_is_exclusive(v_v_1733_)) as u8;
                        if v_isSharedCheck_1753_ == 0 {
                            v___x_1745_ = v_v_1733_;
                            v_isShared_1746_ = v_isSharedCheck_1753_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1743_);
                            crate::leanh::lean_inc(v_key_1742_);
                            crate::leanh::lean_dec(v_v_1733_);
                            v___x_1745_ = crate::leanh::lean_box(0);
                            v_isShared_1746_ = v_isSharedCheck_1753_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1754_ = crate::leanh::lean_ctor_get(v_v_1733_, 0);
                        v_isSharedCheck_1764_ = (!crate::leanh::lean_is_exclusive(v_v_1733_)) as u8;
                        if v_isSharedCheck_1764_ == 0 {
                            v___x_1756_ = v_v_1733_;
                            v_isShared_1757_ = v_isSharedCheck_1764_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1754_);
                            crate::leanh::lean_dec(v_v_1733_);
                            v___x_1756_ = crate::leanh::lean_box(0);
                            v_isShared_1757_ = v_isSharedCheck_1764_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1765_, 0, v_x_1720_);
                        crate::leanh::lean_ctor_set(v___x_1765_, 1, v_x_1721_);
                        v___y_1737_ = v___x_1765_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1738_ = lean_array_fset(v_xs_x27_1735_, v_j_1727_, v___y_1737_);
                crate::leanh::lean_dec(v_j_1727_);
                if v_isShared_1732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1731_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1731_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1740_;
            }
            4 => {
                v___x_1747_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1720_,
                        v_key_1742_,
                    );
                if v___x_1747_ == 0 {
                    crate::leanh::lean_del_object(v___x_1745_);
                    v___x_1748_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1742_,
                        v_val_1743_,
                        v_x_1720_,
                        v_x_1721_,
                    );
                    v___x_1749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1749_, 0, v___x_1748_);
                    v___y_1737_ = v___x_1749_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1743_);
                    crate::leanh::lean_dec(v_key_1742_);
                    if v_isShared_1746_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1745_, 1, v_x_1721_);
                        crate::leanh::lean_ctor_set(v___x_1745_, 0, v_x_1720_);
                        v___x_1751_ = v___x_1745_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1752_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_x_1720_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_x_1721_);
                        v___x_1751_ = v_reuseFailAlloc_1752_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1737_ = v___x_1751_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1758_ = lean_usize_shift_right(v_x_1718_, v___x_1723_);
                v___x_1759_ = lean_usize_add(v_x_1719_, v___x_1724_);
                v___x_1760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_node_1754_, v___x_1758_, v___x_1759_, v_x_1720_, v_x_1721_);
                if v_isShared_1757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1756_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1737_ = v___x_1762_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1772_ == 0 {
                    v___x_1774_ = v___x_1771_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1788_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_ks_1768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_vs_1769_);
                    v___x_1774_ = v_reuseFailAlloc_1788_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1775_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v___x_1774_, v_x_1720_, v_x_1721_);
                v___x_1783_ = 7usize;
                v___x_1784_ = lean_usize_dec_le(v___x_1783_, v_x_1719_);
                if v___x_1784_ == 0 {
                    v___x_1785_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1775_);
                    v___x_1786_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1787_ = lean_nat_dec_lt(v___x_1785_, v___x_1786_);
                    crate::leanh::lean_dec(v___x_1785_);
                    v___y_1777_ = v___x_1787_;
                    state = 10;
                    continue;
                } else {
                    v___y_1777_ = v___x_1784_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1777_ == 0 {
                    v_ks_1778_ = crate::leanh::lean_ctor_get(v_newNode_1775_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1778_);
                    v_vs_1779_ = crate::leanh::lean_ctor_get(v_newNode_1775_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1779_);
                    crate::leanh::lean_dec_ref(v_newNode_1775_);
                    v___x_1780_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0);
                    v___x_1782_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_x_1719_, v_ks_1778_, v_vs_1779_, v___x_1780_, v___x_1781_);
                    crate::leanh::lean_dec_ref(v_vs_1779_);
                    crate::leanh::lean_dec_ref(v_ks_1778_);
                    return v___x_1782_;
                } else {
                    return v_newNode_1775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1790_: usize,
    mut v_keys_1791_: *mut crate::leanh::LeanObject,
    mut v_vals_1792_: *mut crate::leanh::LeanObject,
    mut v_i_1793_: *mut crate::leanh::LeanObject,
    mut v_entries_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v_k_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u64 = 0;
    let mut v_h_1800_: usize = 0;
    let mut v___x_1801_: usize = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: usize = 0;
    let mut v___x_1804_: usize = 0;
    let mut v___x_1805_: usize = 0;
    let mut v_h_1806_: usize = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_array_get_size(v_keys_1791_);
                v___x_1796_ = lean_nat_dec_lt(v_i_1793_, v___x_1795_);
                if v___x_1796_ == 0 {
                    crate::leanh::lean_dec(v_i_1793_);
                    return v_entries_1794_;
                } else {
                    v_k_1797_ = lean_array_fget_borrowed(v_keys_1791_, v_i_1793_);
                    v_v_1798_ = lean_array_fget_borrowed(v_vals_1792_, v_i_1793_);
                    v___x_1799_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1797_);
                    v_h_1800_ = lean_uint64_to_usize(v___x_1799_);
                    v___x_1801_ = 5usize;
                    v___x_1802_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1803_ = 1usize;
                    v___x_1804_ = lean_usize_sub(v_depth_1790_, v___x_1803_);
                    v___x_1805_ = lean_usize_mul(v___x_1801_, v___x_1804_);
                    v_h_1806_ = lean_usize_shift_right(v_h_1800_, v___x_1805_);
                    v___x_1807_ = lean_nat_add(v_i_1793_, v___x_1802_);
                    crate::leanh::lean_dec(v_i_1793_);
                    crate::leanh::lean_inc(v_v_1798_);
                    crate::leanh::lean_inc(v_k_1797_);
                    v___x_1808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_entries_1794_, v_h_1806_, v_depth_1790_, v_k_1797_, v_v_1798_);
                    v_i_1793_ = v___x_1807_;
                    v_entries_1794_ = v___x_1808_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1810_: *mut crate::leanh::LeanObject,
    mut v_keys_1811_: *mut crate::leanh::LeanObject,
    mut v_vals_1812_: *mut crate::leanh::LeanObject,
    mut v_i_1813_: *mut crate::leanh::LeanObject,
    mut v_entries_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1815_: usize = 0;
    let mut v_res_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1815_ = crate::leanh::lean_unbox_usize(v_depth_1810_);
    crate::leanh::lean_dec(v_depth_1810_);
    v_res_1816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1815_, v_keys_1811_, v_vals_1812_, v_i_1813_, v_entries_1814_);
    crate::leanh::lean_dec_ref(v_vals_1812_);
    crate::leanh::lean_dec_ref(v_keys_1811_);
    return v_res_1816_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(
    mut v_x_1817_: *mut crate::leanh::LeanObject,
    mut v_x_1818_: *mut crate::leanh::LeanObject,
    mut v_x_1819_: *mut crate::leanh::LeanObject,
    mut v_x_1820_: *mut crate::leanh::LeanObject,
    mut v_x_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7035__boxed_1822_: usize = 0;
    let mut v_x_7036__boxed_1823_: usize = 0;
    let mut v_res_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7035__boxed_1822_ = crate::leanh::lean_unbox_usize(v_x_1818_);
    crate::leanh::lean_dec(v_x_1818_);
    v_x_7036__boxed_1823_ = crate::leanh::lean_unbox_usize(v_x_1819_);
    crate::leanh::lean_dec(v_x_1819_);
    v_res_1824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_1817_, v_x_7035__boxed_1822_, v_x_7036__boxed_1823_, v_x_1820_, v_x_1821_);
    return v_res_1824_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(
    mut v_x_1825_: *mut crate::leanh::LeanObject,
    mut v_x_1826_: *mut crate::leanh::LeanObject,
    mut v_x_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: u64 = 0;
    let mut v___x_1829_: usize = 0;
    let mut v___x_1830_: usize = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1826_);
    v___x_1829_ = lean_uint64_to_usize(v___x_1828_);
    v___x_1830_ = 1usize;
    v___x_1831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_1825_, v___x_1829_, v___x_1830_, v_x_1826_, v_x_1827_);
    return v___x_1831_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(
    mut v_e_1832_: *mut crate::leanh::LeanObject,
    mut v_xs_1833_: *mut crate::leanh::LeanObject,
    mut v_b_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1839_);
                crate::leanh::lean_inc_ref(v_a_1838_);
                crate::leanh::lean_inc(v_a_1837_);
                crate::leanh::lean_inc_ref(v_a_1836_);
                v___x_1841_ =
                    lean_infer_type(v_e_1832_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
                if crate::leanh::lean_obj_tag(v___x_1841_) == 0 {
                    v_a_1842_ = crate::leanh::lean_ctor_get(v___x_1841_, 0);
                    v_isSharedCheck_1878_ = (!crate::leanh::lean_is_exclusive(v___x_1841_)) as u8;
                    if v_isSharedCheck_1878_ == 0 {
                        v___x_1844_ = v___x_1841_;
                        v_isShared_1845_ = v_isSharedCheck_1878_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1842_);
                        crate::leanh::lean_dec(v___x_1841_);
                        v___x_1844_ = crate::leanh::lean_box(0);
                        v_isShared_1845_ = v_isSharedCheck_1878_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1834_);
                    crate::leanh::lean_dec_ref(v_xs_1833_);
                    return v___x_1841_;
                }
            }
            1 => {
                v___x_1846_ = lean_st_ref_get(v_a_1835_);
                v_funext_1847_ = crate::leanh::lean_ctor_get(v___x_1846_, 3);
                crate::leanh::lean_inc_ref(v_funext_1847_);
                crate::leanh::lean_dec(v___x_1846_);
                v___x_1848_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_funext_1847_, v_a_1842_);
                crate::leanh::lean_dec_ref(v_funext_1847_);
                if crate::leanh::lean_obj_tag(v___x_1848_) == 1 {
                    crate::leanh::lean_dec(v_a_1842_);
                    crate::leanh::lean_dec_ref(v_b_1834_);
                    crate::leanh::lean_dec_ref(v_xs_1833_);
                    v_val_1849_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                    crate::leanh::lean_inc(v_val_1849_);
                    crate::leanh::lean_dec_ref_known(v___x_1848_, 1);
                    if v_isShared_1845_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1844_, 0, v_val_1849_);
                        v___x_1851_ = v___x_1844_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_val_1849_);
                        v___x_1851_ = v_reuseFailAlloc_1852_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1848_);
                    crate::leanh::lean_del_object(v___x_1844_);
                    crate::leanh::lean_inc(v_a_1839_);
                    crate::leanh::lean_inc_ref(v_a_1838_);
                    crate::leanh::lean_inc(v_a_1837_);
                    crate::leanh::lean_inc_ref(v_a_1836_);
                    v___x_1853_ =
                        lean_infer_type(v_b_1834_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
                    if crate::leanh::lean_obj_tag(v___x_1853_) == 0 {
                        v_a_1854_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                        crate::leanh::lean_inc(v_a_1854_);
                        crate::leanh::lean_dec_ref_known(v___x_1853_, 1);
                        v___x_1855_ =
                            l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(
                                v_xs_1833_, v_a_1854_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1855_) == 0 {
                            v_a_1856_ = crate::leanh::lean_ctor_get(v___x_1855_, 0);
                            v_isSharedCheck_1877_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1855_)) as u8;
                            if v_isSharedCheck_1877_ == 0 {
                                v___x_1858_ = v___x_1855_;
                                v_isShared_1859_ = v_isSharedCheck_1877_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1856_);
                                crate::leanh::lean_dec(v___x_1855_);
                                v___x_1858_ = crate::leanh::lean_box(0);
                                v_isShared_1859_ = v_isSharedCheck_1877_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1842_);
                            return v___x_1855_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1842_);
                        crate::leanh::lean_dec_ref(v_xs_1833_);
                        return v___x_1853_;
                    }
                }
            }
            2 => {
                return v___x_1851_;
            }
            3 => {
                v___x_1860_ = lean_st_ref_take(v_a_1835_);
                v_numSteps_1861_ = crate::leanh::lean_ctor_get(v___x_1860_, 0);
                v_persistentCache_1862_ = crate::leanh::lean_ctor_get(v___x_1860_, 1);
                v_transientCache_1863_ = crate::leanh::lean_ctor_get(v___x_1860_, 2);
                v_funext_1864_ = crate::leanh::lean_ctor_get(v___x_1860_, 3);
                v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v___x_1860_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v___x_1866_ = v___x_1860_;
                    v_isShared_1867_ = v_isSharedCheck_1876_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_funext_1864_);
                    crate::leanh::lean_inc(v_transientCache_1863_);
                    crate::leanh::lean_inc(v_persistentCache_1862_);
                    crate::leanh::lean_inc(v_numSteps_1861_);
                    crate::leanh::lean_dec(v___x_1860_);
                    v___x_1866_ = crate::leanh::lean_box(0);
                    v_isShared_1867_ = v_isSharedCheck_1876_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1856_);
                v___x_1868_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_funext_1864_, v_a_1842_, v_a_1856_);
                if v_isShared_1867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1866_, 3, v___x_1868_);
                    v___x_1870_ = v___x_1866_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_numSteps_1861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_persistentCache_1862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_transientCache_1863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 3, v___x_1868_);
                    v___x_1870_ = v_reuseFailAlloc_1875_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1871_ = lean_st_ref_set(v_a_1835_, v___x_1870_);
                if v_isShared_1859_ == 0 {
                    v___x_1873_ = v___x_1858_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1856_);
                    v___x_1873_ = v_reuseFailAlloc_1874_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(
    mut v_e_1879_: *mut crate::leanh::LeanObject,
    mut v_xs_1880_: *mut crate::leanh::LeanObject,
    mut v_b_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_1879_, v_xs_1880_, v_b_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
    crate::leanh::lean_dec(v_a_1886_);
    crate::leanh::lean_dec_ref(v_a_1885_);
    crate::leanh::lean_dec(v_a_1884_);
    crate::leanh::lean_dec_ref(v_a_1883_);
    crate::leanh::lean_dec(v_a_1882_);
    return v_res_1888_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(
    mut v_e_1889_: *mut crate::leanh::LeanObject,
    mut v_xs_1890_: *mut crate::leanh::LeanObject,
    mut v_b_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_1889_, v_xs_1890_, v_b_1891_, v_a_1894_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
    return v___x_1902_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(
    mut v_e_1903_: *mut crate::leanh::LeanObject,
    mut v_xs_1904_: *mut crate::leanh::LeanObject,
    mut v_b_1905_: *mut crate::leanh::LeanObject,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
    mut v_a_1909_: *mut crate::leanh::LeanObject,
    mut v_a_1910_: *mut crate::leanh::LeanObject,
    mut v_a_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
    mut v_a_1913_: *mut crate::leanh::LeanObject,
    mut v_a_1914_: *mut crate::leanh::LeanObject,
    mut v_a_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ =
        l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(
            v_e_1903_, v_xs_1904_, v_b_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_,
            v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_,
        );
    crate::leanh::lean_dec(v_a_1914_);
    crate::leanh::lean_dec_ref(v_a_1913_);
    crate::leanh::lean_dec(v_a_1912_);
    crate::leanh::lean_dec_ref(v_a_1911_);
    crate::leanh::lean_dec(v_a_1910_);
    crate::leanh::lean_dec_ref(v_a_1909_);
    crate::leanh::lean_dec(v_a_1908_);
    crate::leanh::lean_dec_ref(v_a_1907_);
    crate::leanh::lean_dec(v_a_1906_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(
    mut v_00_u03b2_1917_: *mut crate::leanh::LeanObject,
    mut v_x_1918_: *mut crate::leanh::LeanObject,
    mut v_x_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_1918_, v_x_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(
    mut v_00_u03b2_1921_: *mut crate::leanh::LeanObject,
    mut v_x_1922_: *mut crate::leanh::LeanObject,
    mut v_x_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(v_00_u03b2_1921_, v_x_1922_, v_x_1923_);
    crate::leanh::lean_dec_ref(v_x_1923_);
    crate::leanh::lean_dec_ref(v_x_1922_);
    return v_res_1924_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(
    mut v_00_u03b2_1925_: *mut crate::leanh::LeanObject,
    mut v_x_1926_: *mut crate::leanh::LeanObject,
    mut v_x_1927_: *mut crate::leanh::LeanObject,
    mut v_x_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_x_1926_, v_x_1927_, v_x_1928_);
    return v___x_1929_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(
    mut v_00_u03b2_1930_: *mut crate::leanh::LeanObject,
    mut v_x_1931_: *mut crate::leanh::LeanObject,
    mut v_x_1932_: usize,
    mut v_x_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_1931_, v_x_1932_, v_x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(
    mut v_00_u03b2_1935_: *mut crate::leanh::LeanObject,
    mut v_x_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7298__boxed_1939_: usize = 0;
    let mut v_res_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7298__boxed_1939_ = crate::leanh::lean_unbox_usize(v_x_1937_);
    crate::leanh::lean_dec(v_x_1937_);
    v_res_1940_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(v_00_u03b2_1935_, v_x_1936_, v_x_7298__boxed_1939_, v_x_1938_);
    crate::leanh::lean_dec_ref(v_x_1938_);
    crate::leanh::lean_dec_ref(v_x_1936_);
    return v_res_1940_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(
    mut v_00_u03b2_1941_: *mut crate::leanh::LeanObject,
    mut v_x_1942_: *mut crate::leanh::LeanObject,
    mut v_x_1943_: usize,
    mut v_x_1944_: usize,
    mut v_x_1945_: *mut crate::leanh::LeanObject,
    mut v_x_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_1942_, v_x_1943_, v_x_1944_, v_x_1945_, v_x_1946_);
    return v___x_1947_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(
    mut v_00_u03b2_1948_: *mut crate::leanh::LeanObject,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
    mut v_x_1951_: *mut crate::leanh::LeanObject,
    mut v_x_1952_: *mut crate::leanh::LeanObject,
    mut v_x_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7309__boxed_1954_: usize = 0;
    let mut v_x_7310__boxed_1955_: usize = 0;
    let mut v_res_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7309__boxed_1954_ = crate::leanh::lean_unbox_usize(v_x_1950_);
    crate::leanh::lean_dec(v_x_1950_);
    v_x_7310__boxed_1955_ = crate::leanh::lean_unbox_usize(v_x_1951_);
    crate::leanh::lean_dec(v_x_1951_);
    v_res_1956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(v_00_u03b2_1948_, v_x_1949_, v_x_7309__boxed_1954_, v_x_7310__boxed_1955_, v_x_1952_, v_x_1953_);
    return v_res_1956_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1957_: *mut crate::leanh::LeanObject,
    mut v_keys_1958_: *mut crate::leanh::LeanObject,
    mut v_vals_1959_: *mut crate::leanh::LeanObject,
    mut v_heq_1960_: *mut crate::leanh::LeanObject,
    mut v_i_1961_: *mut crate::leanh::LeanObject,
    mut v_k_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_1958_, v_vals_1959_, v_i_1961_, v_k_1962_);
    return v___x_1963_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1964_: *mut crate::leanh::LeanObject,
    mut v_keys_1965_: *mut crate::leanh::LeanObject,
    mut v_vals_1966_: *mut crate::leanh::LeanObject,
    mut v_heq_1967_: *mut crate::leanh::LeanObject,
    mut v_i_1968_: *mut crate::leanh::LeanObject,
    mut v_k_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(v_00_u03b2_1964_, v_keys_1965_, v_vals_1966_, v_heq_1967_, v_i_1968_, v_k_1969_);
    crate::leanh::lean_dec_ref(v_k_1969_);
    crate::leanh::lean_dec_ref(v_vals_1966_);
    crate::leanh::lean_dec_ref(v_keys_1965_);
    return v_res_1970_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1971_: *mut crate::leanh::LeanObject,
    mut v_n_1972_: *mut crate::leanh::LeanObject,
    mut v_k_1973_: *mut crate::leanh::LeanObject,
    mut v_v_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v_n_1972_, v_k_1973_, v_v_1974_);
    return v___x_1975_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1976_: *mut crate::leanh::LeanObject,
    mut v_depth_1977_: usize,
    mut v_keys_1978_: *mut crate::leanh::LeanObject,
    mut v_vals_1979_: *mut crate::leanh::LeanObject,
    mut v_heq_1980_: *mut crate::leanh::LeanObject,
    mut v_i_1981_: *mut crate::leanh::LeanObject,
    mut v_entries_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_1977_, v_keys_1978_, v_vals_1979_, v_i_1981_, v_entries_1982_);
    return v___x_1983_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1984_: *mut crate::leanh::LeanObject,
    mut v_depth_1985_: *mut crate::leanh::LeanObject,
    mut v_keys_1986_: *mut crate::leanh::LeanObject,
    mut v_vals_1987_: *mut crate::leanh::LeanObject,
    mut v_heq_1988_: *mut crate::leanh::LeanObject,
    mut v_i_1989_: *mut crate::leanh::LeanObject,
    mut v_entries_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1991_: usize = 0;
    let mut v_res_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1991_ = crate::leanh::lean_unbox_usize(v_depth_1985_);
    crate::leanh::lean_dec(v_depth_1985_);
    v_res_1992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(v_00_u03b2_1984_, v_depth_boxed_1991_, v_keys_1986_, v_vals_1987_, v_heq_1988_, v_i_1989_, v_entries_1990_);
    crate::leanh::lean_dec_ref(v_vals_1987_);
    crate::leanh::lean_dec_ref(v_keys_1986_);
    return v_res_1992_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1993_: *mut crate::leanh::LeanObject,
    mut v_x_1994_: *mut crate::leanh::LeanObject,
    mut v_x_1995_: *mut crate::leanh::LeanObject,
    mut v_x_1996_: *mut crate::leanh::LeanObject,
    mut v_x_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1994_, v_x_1995_, v_x_1996_, v_x_1997_);
    return v___x_1998_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(
    mut v_simpBody_1999_: *mut crate::leanh::LeanObject,
    mut v_e_2000_: *mut crate::leanh::LeanObject,
    mut v_xs_2001_: *mut crate::leanh::LeanObject,
    mut v_b_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
    mut v_a_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v_contextDependent_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2025_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: u8 = 0;
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_a_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2078_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2082_: u8 = 0;
    let mut v_isSharedCheck_2083_: u8 = 0;
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2011_);
                crate::leanh::lean_inc_ref(v_a_2010_);
                crate::leanh::lean_inc(v_a_2009_);
                crate::leanh::lean_inc_ref(v_a_2008_);
                crate::leanh::lean_inc(v_a_2007_);
                crate::leanh::lean_inc_ref(v_a_2006_);
                crate::leanh::lean_inc(v_a_2005_);
                crate::leanh::lean_inc_ref(v_a_2004_);
                crate::leanh::lean_inc(v_a_2003_);
                crate::leanh::lean_inc_ref(v_b_2002_);
                v___x_2013_ = crate::leanh::lean_apply_11(
                    v_simpBody_1999_,
                    v_b_2002_,
                    v_a_2003_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                    v_a_2008_,
                    v_a_2009_,
                    v_a_2010_,
                    v_a_2011_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2013_) == 0 {
                    v_a_2014_ = crate::leanh::lean_ctor_get(v___x_2013_, 0);
                    v_isSharedCheck_2084_ = (!crate::leanh::lean_is_exclusive(v___x_2013_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v___x_2016_ = v___x_2013_;
                        v_isShared_2017_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2014_);
                        crate::leanh::lean_dec(v___x_2013_);
                        v___x_2016_ = crate::leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2002_);
                    crate::leanh::lean_dec_ref(v_xs_2001_);
                    crate::leanh::lean_dec_ref(v_e_2000_);
                    return v___x_2013_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2014_) == 0 {
                    crate::leanh::lean_dec_ref(v_b_2002_);
                    crate::leanh::lean_dec_ref(v_xs_2001_);
                    crate::leanh::lean_dec_ref(v_e_2000_);
                    v_contextDependent_2018_ =
                        crate::leanh::lean_ctor_get_uint8(v_a_2014_, 1 as u32);
                    crate::leanh::lean_dec_ref_known(v_a_2014_, 0);
                    v___x_2019_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2018_);
                    if v_isShared_2017_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2016_, 0, v___x_2019_);
                        v___x_2021_ = v___x_2016_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
                        v___x_2021_ = v_reuseFailAlloc_2022_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2016_);
                    v_e_x27_2023_ = crate::leanh::lean_ctor_get(v_a_2014_, 0);
                    v_proof_2024_ = crate::leanh::lean_ctor_get(v_a_2014_, 1);
                    v_contextDependent_2025_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2014_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_2083_ = (!crate::leanh::lean_is_exclusive(v_a_2014_)) as u8;
                    if v_isSharedCheck_2083_ == 0 {
                        v___x_2027_ = v_a_2014_;
                        v_isShared_2028_ = v_isSharedCheck_2083_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_proof_2024_);
                        crate::leanh::lean_inc(v_e_x27_2023_);
                        crate::leanh::lean_dec(v_a_2014_);
                        v___x_2027_ = crate::leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2083_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2021_;
            }
            3 => {
                v___x_2029_ = 0;
                v___x_2030_ = 1;
                v___x_2031_ = 1;
                v___x_2032_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_2001_,
                    v_proof_2024_,
                    v___x_2029_,
                    v___x_2030_,
                    v___x_2029_,
                    v___x_2030_,
                    v___x_2031_,
                    v_a_2008_,
                    v_a_2009_,
                    v_a_2010_,
                    v_a_2011_,
                );
                if crate::leanh::lean_obj_tag(v___x_2032_) == 0 {
                    v_a_2033_ = crate::leanh::lean_ctor_get(v___x_2032_, 0);
                    crate::leanh::lean_inc(v_a_2033_);
                    crate::leanh::lean_dec_ref_known(v___x_2032_, 1);
                    v___x_2034_ = l_Lean_Meta_mkLambdaFVars(
                        v_xs_2001_,
                        v_e_x27_2023_,
                        v___x_2029_,
                        v___x_2030_,
                        v___x_2029_,
                        v___x_2030_,
                        v___x_2031_,
                        v_a_2008_,
                        v_a_2009_,
                        v_a_2010_,
                        v_a_2011_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2034_) == 0 {
                        v_a_2035_ = crate::leanh::lean_ctor_get(v___x_2034_, 0);
                        crate::leanh::lean_inc(v_a_2035_);
                        crate::leanh::lean_dec_ref_known(v___x_2034_, 1);
                        v___x_2036_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2035_, v_a_2007_);
                        if crate::leanh::lean_obj_tag(v___x_2036_) == 0 {
                            v_a_2037_ = crate::leanh::lean_ctor_get(v___x_2036_, 0);
                            crate::leanh::lean_inc(v_a_2037_);
                            crate::leanh::lean_dec_ref_known(v___x_2036_, 1);
                            crate::leanh::lean_inc_ref(v_e_2000_);
                            v___x_2038_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_2000_, v_xs_2001_, v_b_2002_, v_a_2005_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
                            if crate::leanh::lean_obj_tag(v___x_2038_) == 0 {
                                v_a_2039_ = crate::leanh::lean_ctor_get(v___x_2038_, 0);
                                v_isSharedCheck_2050_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2038_)) as u8;
                                if v_isSharedCheck_2050_ == 0 {
                                    v___x_2041_ = v___x_2038_;
                                    v_isShared_2042_ = v_isSharedCheck_2050_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2039_);
                                    crate::leanh::lean_dec(v___x_2038_);
                                    v___x_2041_ = crate::leanh::lean_box(0);
                                    v_isShared_2042_ = v_isSharedCheck_2050_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2037_);
                                crate::leanh::lean_dec(v_a_2033_);
                                crate::leanh::lean_del_object(v___x_2027_);
                                crate::leanh::lean_dec_ref(v_e_2000_);
                                v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2038_, 0);
                                v_isSharedCheck_2058_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2038_)) as u8;
                                if v_isSharedCheck_2058_ == 0 {
                                    v___x_2053_ = v___x_2038_;
                                    v_isShared_2054_ = v_isSharedCheck_2058_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2051_);
                                    crate::leanh::lean_dec(v___x_2038_);
                                    v___x_2053_ = crate::leanh::lean_box(0);
                                    v_isShared_2054_ = v_isSharedCheck_2058_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2033_);
                            crate::leanh::lean_del_object(v___x_2027_);
                            crate::leanh::lean_dec_ref(v_b_2002_);
                            crate::leanh::lean_dec_ref(v_xs_2001_);
                            crate::leanh::lean_dec_ref(v_e_2000_);
                            v_a_2059_ = crate::leanh::lean_ctor_get(v___x_2036_, 0);
                            v_isSharedCheck_2066_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2036_)) as u8;
                            if v_isSharedCheck_2066_ == 0 {
                                v___x_2061_ = v___x_2036_;
                                v_isShared_2062_ = v_isSharedCheck_2066_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2059_);
                                crate::leanh::lean_dec(v___x_2036_);
                                v___x_2061_ = crate::leanh::lean_box(0);
                                v_isShared_2062_ = v_isSharedCheck_2066_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2033_);
                        crate::leanh::lean_del_object(v___x_2027_);
                        crate::leanh::lean_dec_ref(v_b_2002_);
                        crate::leanh::lean_dec_ref(v_xs_2001_);
                        crate::leanh::lean_dec_ref(v_e_2000_);
                        v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2034_, 0);
                        v_isSharedCheck_2074_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2034_)) as u8;
                        if v_isSharedCheck_2074_ == 0 {
                            v___x_2069_ = v___x_2034_;
                            v_isShared_2070_ = v_isSharedCheck_2074_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2067_);
                            crate::leanh::lean_dec(v___x_2034_);
                            v___x_2069_ = crate::leanh::lean_box(0);
                            v_isShared_2070_ = v_isSharedCheck_2074_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2027_);
                    crate::leanh::lean_dec_ref(v_e_x27_2023_);
                    crate::leanh::lean_dec_ref(v_b_2002_);
                    crate::leanh::lean_dec_ref(v_xs_2001_);
                    crate::leanh::lean_dec_ref(v_e_2000_);
                    v_a_2075_ = crate::leanh::lean_ctor_get(v___x_2032_, 0);
                    v_isSharedCheck_2082_ = (!crate::leanh::lean_is_exclusive(v___x_2032_)) as u8;
                    if v_isSharedCheck_2082_ == 0 {
                        v___x_2077_ = v___x_2032_;
                        v_isShared_2078_ = v_isSharedCheck_2082_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2075_);
                        crate::leanh::lean_dec(v___x_2032_);
                        v___x_2077_ = crate::leanh::lean_box(0);
                        v_isShared_2078_ = v_isSharedCheck_2082_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_2037_);
                v___x_2043_ = l_Lean_mkApp3(v_a_2039_, v_e_2000_, v_a_2037_, v_a_2033_);
                if v_isShared_2028_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2027_, 1, v___x_2043_);
                    crate::leanh::lean_ctor_set(v___x_2027_, 0, v_a_2037_);
                    v___x_2045_ = v___x_2027_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2043_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2049_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_2025_,
                    );
                    v___x_2045_ = v_reuseFailAlloc_2049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2045_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2029_,
                );
                if v_isShared_2042_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2041_, 0, v___x_2045_);
                    v___x_2047_ = v___x_2041_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2047_;
            }
            7 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2056_;
            }
            9 => {
                if v_isShared_2062_ == 0 {
                    v___x_2064_ = v___x_2061_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2064_;
            }
            11 => {
                if v_isShared_2070_ == 0 {
                    v___x_2072_ = v___x_2069_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2072_;
            }
            13 => {
                if v_isShared_2078_ == 0 {
                    v___x_2080_ = v___x_2077_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2081_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
                    v___x_2080_ = v_reuseFailAlloc_2081_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(
    mut v_simpBody_2085_: *mut crate::leanh::LeanObject,
    mut v_e_2086_: *mut crate::leanh::LeanObject,
    mut v_xs_2087_: *mut crate::leanh::LeanObject,
    mut v_b_2088_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2099_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(
        v_simpBody_2085_,
        v_e_2086_,
        v_xs_2087_,
        v_b_2088_,
        v_a_2089_,
        v_a_2090_,
        v_a_2091_,
        v_a_2092_,
        v_a_2093_,
        v_a_2094_,
        v_a_2095_,
        v_a_2096_,
        v_a_2097_,
    );
    crate::leanh::lean_dec(v_a_2097_);
    crate::leanh::lean_dec_ref(v_a_2096_);
    crate::leanh::lean_dec(v_a_2095_);
    crate::leanh::lean_dec_ref(v_a_2094_);
    crate::leanh::lean_dec(v_a_2093_);
    crate::leanh::lean_dec_ref(v_a_2092_);
    crate::leanh::lean_dec(v_a_2091_);
    crate::leanh::lean_dec_ref(v_a_2090_);
    crate::leanh::lean_dec(v_a_2089_);
    return v_res_2099_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(
    mut v_k_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v_b_2106_: *mut crate::leanh::LeanObject,
    mut v_c_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
    mut v___y_2109_: *mut crate::leanh::LeanObject,
    mut v___y_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2111_);
    crate::leanh::lean_inc_ref(v___y_2110_);
    crate::leanh::lean_inc(v___y_2109_);
    crate::leanh::lean_inc_ref(v___y_2108_);
    crate::leanh::lean_inc(v___y_2105_);
    crate::leanh::lean_inc_ref(v___y_2104_);
    crate::leanh::lean_inc(v___y_2103_);
    crate::leanh::lean_inc_ref(v___y_2102_);
    crate::leanh::lean_inc(v___y_2101_);
    v___x_2113_ = crate::leanh::lean_apply_12(
        v_k_2100_,
        v_b_2106_,
        v_c_2107_,
        v___y_2101_,
        v___y_2102_,
        v___y_2103_,
        v___y_2104_,
        v___y_2105_,
        v___y_2108_,
        v___y_2109_,
        v___y_2110_,
        v___y_2111_,
        crate::leanh::lean_box(0),
    );
    return v___x_2113_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(
    mut v_k_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v_b_2120_: *mut crate::leanh::LeanObject,
    mut v_c_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
    mut v___y_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(v_k_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v_b_2120_, v_c_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
    crate::leanh::lean_dec(v___y_2125_);
    crate::leanh::lean_dec_ref(v___y_2124_);
    crate::leanh::lean_dec(v___y_2123_);
    crate::leanh::lean_dec_ref(v___y_2122_);
    crate::leanh::lean_dec(v___y_2119_);
    crate::leanh::lean_dec_ref(v___y_2118_);
    crate::leanh::lean_dec(v___y_2117_);
    crate::leanh::lean_dec_ref(v___y_2116_);
    crate::leanh::lean_dec(v___y_2115_);
    return v_res_2127_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(
    mut v_e_2128_: *mut crate::leanh::LeanObject,
    mut v_k_2129_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2130_: u8,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: u8 = 0;
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2149_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2135_);
                crate::leanh::lean_inc_ref(v___y_2134_);
                crate::leanh::lean_inc(v___y_2133_);
                crate::leanh::lean_inc_ref(v___y_2132_);
                crate::leanh::lean_inc(v___y_2131_);
                v___f_2141_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 6);
                crate::leanh::lean_closure_set(v___f_2141_, 0, v_k_2129_);
                crate::leanh::lean_closure_set(v___f_2141_, 1, v___y_2131_);
                crate::leanh::lean_closure_set(v___f_2141_, 2, v___y_2132_);
                crate::leanh::lean_closure_set(v___f_2141_, 3, v___y_2133_);
                crate::leanh::lean_closure_set(v___f_2141_, 4, v___y_2134_);
                crate::leanh::lean_closure_set(v___f_2141_, 5, v___y_2135_);
                v___x_2142_ = 1;
                v___x_2143_ = 0;
                v___x_2144_ = crate::leanh::lean_box(0);
                v___x_2145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_2128_,
                    v___x_2142_,
                    v___x_2143_,
                    v___x_2142_,
                    v___x_2143_,
                    v___x_2144_,
                    v___f_2141_,
                    v_cleanupAnnotations_2130_,
                    v___y_2136_,
                    v___y_2137_,
                    v___y_2138_,
                    v___y_2139_,
                );
                if crate::leanh::lean_obj_tag(v___x_2145_) == 0 {
                    return v___x_2145_;
                } else {
                    v_a_2146_ = crate::leanh::lean_ctor_get(v___x_2145_, 0);
                    v_isSharedCheck_2153_ = (!crate::leanh::lean_is_exclusive(v___x_2145_)) as u8;
                    if v_isSharedCheck_2153_ == 0 {
                        v___x_2148_ = v___x_2145_;
                        v_isShared_2149_ = v_isSharedCheck_2153_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2146_);
                        crate::leanh::lean_dec(v___x_2145_);
                        v___x_2148_ = crate::leanh::lean_box(0);
                        v_isShared_2149_ = v_isSharedCheck_2153_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2149_ == 0 {
                    v___x_2151_ = v___x_2148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
                    v___x_2151_ = v_reuseFailAlloc_2152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(
    mut v_e_2154_: *mut crate::leanh::LeanObject,
    mut v_k_2155_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2167_: u8 = 0;
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2167_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2156_) as u8);
    v_res_2168_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(
            v_e_2154_,
            v_k_2155_,
            v_cleanupAnnotations_boxed_2167_,
            v___y_2157_,
            v___y_2158_,
            v___y_2159_,
            v___y_2160_,
            v___y_2161_,
            v___y_2162_,
            v___y_2163_,
            v___y_2164_,
            v___y_2165_,
        );
    crate::leanh::lean_dec(v___y_2165_);
    crate::leanh::lean_dec_ref(v___y_2164_);
    crate::leanh::lean_dec(v___y_2163_);
    crate::leanh::lean_dec_ref(v___y_2162_);
    crate::leanh::lean_dec(v___y_2161_);
    crate::leanh::lean_dec_ref(v___y_2160_);
    crate::leanh::lean_dec(v___y_2159_);
    crate::leanh::lean_dec_ref(v___y_2158_);
    crate::leanh::lean_dec(v___y_2157_);
    return v_res_2168_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(
    mut v_00_u03b1_2169_: *mut crate::leanh::LeanObject,
    mut v_e_2170_: *mut crate::leanh::LeanObject,
    mut v_k_2171_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2172_: u8,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
    mut v___y_2175_: *mut crate::leanh::LeanObject,
    mut v___y_2176_: *mut crate::leanh::LeanObject,
    mut v___y_2177_: *mut crate::leanh::LeanObject,
    mut v___y_2178_: *mut crate::leanh::LeanObject,
    mut v___y_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(
            v_e_2170_,
            v_k_2171_,
            v_cleanupAnnotations_2172_,
            v___y_2173_,
            v___y_2174_,
            v___y_2175_,
            v___y_2176_,
            v___y_2177_,
            v___y_2178_,
            v___y_2179_,
            v___y_2180_,
            v___y_2181_,
        );
    return v___x_2183_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(
    mut v_00_u03b1_2184_: *mut crate::leanh::LeanObject,
    mut v_e_2185_: *mut crate::leanh::LeanObject,
    mut v_k_2186_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2198_: u8 = 0;
    let mut v_res_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2198_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2187_) as u8);
    v_res_2199_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(
        v_00_u03b1_2184_,
        v_e_2185_,
        v_k_2186_,
        v_cleanupAnnotations_boxed_2198_,
        v___y_2188_,
        v___y_2189_,
        v___y_2190_,
        v___y_2191_,
        v___y_2192_,
        v___y_2193_,
        v___y_2194_,
        v___y_2195_,
        v___y_2196_,
    );
    crate::leanh::lean_dec(v___y_2196_);
    crate::leanh::lean_dec_ref(v___y_2195_);
    crate::leanh::lean_dec(v___y_2194_);
    crate::leanh::lean_dec_ref(v___y_2193_);
    crate::leanh::lean_dec(v___y_2192_);
    crate::leanh::lean_dec_ref(v___y_2191_);
    crate::leanh::lean_dec(v___y_2190_);
    crate::leanh::lean_dec_ref(v___y_2189_);
    crate::leanh::lean_dec(v___y_2188_);
    return v_res_2199_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v_transientCache_2201_: *mut crate::leanh::LeanObject,
    mut v_funext_2202_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_unused_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2205_ = lean_st_ref_take(v___y_2200_);
                v_numSteps_2206_ = crate::leanh::lean_ctor_get(v___x_2205_, 0);
                v_persistentCache_2207_ = crate::leanh::lean_ctor_get(v___x_2205_, 1);
                v_isSharedCheck_2217_ = (!crate::leanh::lean_is_exclusive(v___x_2205_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v_unused_2218_ = crate::leanh::lean_ctor_get(v___x_2205_, 3);
                    crate::leanh::lean_dec(v_unused_2218_);
                    v_unused_2219_ = crate::leanh::lean_ctor_get(v___x_2205_, 2);
                    crate::leanh::lean_dec(v_unused_2219_);
                    v___x_2209_ = v___x_2205_;
                    v_isShared_2210_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_persistentCache_2207_);
                    crate::leanh::lean_inc(v_numSteps_2206_);
                    crate::leanh::lean_dec(v___x_2205_);
                    v___x_2209_ = crate::leanh::lean_box(0);
                    v_isShared_2210_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2209_, 3, v_funext_2202_);
                    crate::leanh::lean_ctor_set(v___x_2209_, 2, v_transientCache_2201_);
                    v___x_2212_ = v___x_2209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_numSteps_2206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_persistentCache_2207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_transientCache_2201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_funext_2202_);
                    v___x_2212_ = v_reuseFailAlloc_2216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2213_ = lean_st_ref_set(v___y_2200_, v___x_2212_);
                v___x_2214_ = crate::leanh::lean_box(0);
                v___x_2215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2214_);
                return v___x_2215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v_transientCache_2221_: *mut crate::leanh::LeanObject,
    mut v_funext_2222_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2225_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(
        v___y_2220_,
        v_transientCache_2221_,
        v_funext_2222_,
        v_a_x3f_2223_,
    );
    crate::leanh::lean_dec(v_a_x3f_2223_);
    crate::leanh::lean_dec(v___y_2220_);
    return v_res_2225_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(
    mut v_simpBody_2226_: *mut crate::leanh::LeanObject,
    mut v_e_2227_: *mut crate::leanh::LeanObject,
    mut v_xs_2228_: *mut crate::leanh::LeanObject,
    mut v_b_2229_: *mut crate::leanh::LeanObject,
    mut v___y_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut v_unused_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut v_unused_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_a_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2240_ = lean_st_ref_get(v___y_2232_);
                v___x_2241_ = lean_st_ref_get(v___y_2232_);
                v_transientCache_2242_ = crate::leanh::lean_ctor_get(v___x_2240_, 2);
                crate::leanh::lean_inc_ref(v_transientCache_2242_);
                crate::leanh::lean_dec(v___x_2240_);
                v_funext_2243_ = crate::leanh::lean_ctor_get(v___x_2241_, 3);
                crate::leanh::lean_inc_ref(v_funext_2243_);
                crate::leanh::lean_dec(v___x_2241_);
                v___x_2256_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_2229_, v___y_2234_);
                if crate::leanh::lean_obj_tag(v___x_2256_) == 0 {
                    v_a_2257_ = crate::leanh::lean_ctor_get(v___x_2256_, 0);
                    crate::leanh::lean_inc(v_a_2257_);
                    crate::leanh::lean_dec_ref_known(v___x_2256_, 1);
                    v___x_2258_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_2226_, v_e_2227_, v_xs_2228_, v_a_2257_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
                    if crate::leanh::lean_obj_tag(v___x_2258_) == 0 {
                        v_a_2259_ = crate::leanh::lean_ctor_get(v___x_2258_, 0);
                        v_isSharedCheck_2275_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2258_)) as u8;
                        if v_isSharedCheck_2275_ == 0 {
                            v___x_2261_ = v___x_2258_;
                            v_isShared_2262_ = v_isSharedCheck_2275_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2259_);
                            crate::leanh::lean_dec(v___x_2258_);
                            v___x_2261_ = crate::leanh::lean_box(0);
                            v_isShared_2262_ = v_isSharedCheck_2275_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_2276_ = crate::leanh::lean_ctor_get(v___x_2258_, 0);
                        crate::leanh::lean_inc(v_a_2276_);
                        crate::leanh::lean_dec_ref_known(v___x_2258_, 1);
                        v_a_2245_ = v_a_2276_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_xs_2228_);
                    crate::leanh::lean_dec_ref(v_e_2227_);
                    crate::leanh::lean_dec_ref(v_simpBody_2226_);
                    v_a_2277_ = crate::leanh::lean_ctor_get(v___x_2256_, 0);
                    crate::leanh::lean_inc(v_a_2277_);
                    crate::leanh::lean_dec_ref_known(v___x_2256_, 1);
                    v_a_2245_ = v_a_2277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2246_ = crate::leanh::lean_box(0);
                v___x_2247_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(
                    v___y_2232_,
                    v_transientCache_2242_,
                    v_funext_2243_,
                    v___x_2246_,
                );
                v_isSharedCheck_2254_ = (!crate::leanh::lean_is_exclusive(v___x_2247_)) as u8;
                if v_isSharedCheck_2254_ == 0 {
                    v_unused_2255_ = crate::leanh::lean_ctor_get(v___x_2247_, 0);
                    crate::leanh::lean_dec(v_unused_2255_);
                    v___x_2249_ = v___x_2247_;
                    v_isShared_2250_ = v_isSharedCheck_2254_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2247_);
                    v___x_2249_ = crate::leanh::lean_box(0);
                    v_isShared_2250_ = v_isSharedCheck_2254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2250_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2249_, 1);
                    crate::leanh::lean_ctor_set(v___x_2249_, 0, v_a_2245_);
                    v___x_2252_ = v___x_2249_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2245_);
                    v___x_2252_ = v_reuseFailAlloc_2253_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2252_;
            }
            4 => {
                crate::leanh::lean_inc(v_a_2259_);
                if v_isShared_2262_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2261_, 1);
                    v___x_2264_ = v___x_2261_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2259_);
                    v___x_2264_ = v_reuseFailAlloc_2274_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2265_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(
                    v___y_2232_,
                    v_transientCache_2242_,
                    v_funext_2243_,
                    v___x_2264_,
                );
                crate::leanh::lean_dec_ref(v___x_2264_);
                v_isSharedCheck_2272_ = (!crate::leanh::lean_is_exclusive(v___x_2265_)) as u8;
                if v_isSharedCheck_2272_ == 0 {
                    v_unused_2273_ = crate::leanh::lean_ctor_get(v___x_2265_, 0);
                    crate::leanh::lean_dec(v_unused_2273_);
                    v___x_2267_ = v___x_2265_;
                    v_isShared_2268_ = v_isSharedCheck_2272_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2265_);
                    v___x_2267_ = crate::leanh::lean_box(0);
                    v_isShared_2268_ = v_isSharedCheck_2272_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2267_, 0, v_a_2259_);
                    v___x_2270_ = v___x_2267_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2259_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(
    mut v_simpBody_2278_: *mut crate::leanh::LeanObject,
    mut v_e_2279_: *mut crate::leanh::LeanObject,
    mut v_xs_2280_: *mut crate::leanh::LeanObject,
    mut v_b_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2292_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(
        v_simpBody_2278_,
        v_e_2279_,
        v_xs_2280_,
        v_b_2281_,
        v___y_2282_,
        v___y_2283_,
        v___y_2284_,
        v___y_2285_,
        v___y_2286_,
        v___y_2287_,
        v___y_2288_,
        v___y_2289_,
        v___y_2290_,
    );
    crate::leanh::lean_dec(v___y_2290_);
    crate::leanh::lean_dec_ref(v___y_2289_);
    crate::leanh::lean_dec(v___y_2288_);
    crate::leanh::lean_dec_ref(v___y_2287_);
    crate::leanh::lean_dec(v___y_2286_);
    crate::leanh::lean_dec_ref(v___y_2285_);
    crate::leanh::lean_dec(v___y_2284_);
    crate::leanh::lean_dec_ref(v___y_2283_);
    crate::leanh::lean_dec(v___y_2282_);
    return v_res_2292_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda_x27(
    mut v_simpBody_2293_: *mut crate::leanh::LeanObject,
    mut v_e_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
    mut v_a_2301_: *mut crate::leanh::LeanObject,
    mut v_a_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2294_);
    v___f_2305_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed as *mut core::ffi::c_void,
        14,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2305_, 0, v_simpBody_2293_);
    crate::leanh::lean_closure_set(v___f_2305_, 1, v_e_2294_);
    v___x_2306_ = 0;
    v___x_2307_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(
            v_e_2294_,
            v___f_2305_,
            v___x_2306_,
            v_a_2295_,
            v_a_2296_,
            v_a_2297_,
            v_a_2298_,
            v_a_2299_,
            v_a_2300_,
            v_a_2301_,
            v_a_2302_,
            v_a_2303_,
        );
    return v___x_2307_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(
    mut v_simpBody_2308_: *mut crate::leanh::LeanObject,
    mut v_e_2309_: *mut crate::leanh::LeanObject,
    mut v_a_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
    mut v_a_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v_a_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(
        v_simpBody_2308_,
        v_e_2309_,
        v_a_2310_,
        v_a_2311_,
        v_a_2312_,
        v_a_2313_,
        v_a_2314_,
        v_a_2315_,
        v_a_2316_,
        v_a_2317_,
        v_a_2318_,
    );
    crate::leanh::lean_dec(v_a_2318_);
    crate::leanh::lean_dec_ref(v_a_2317_);
    crate::leanh::lean_dec(v_a_2316_);
    crate::leanh::lean_dec_ref(v_a_2315_);
    crate::leanh::lean_dec(v_a_2314_);
    crate::leanh::lean_dec_ref(v_a_2313_);
    crate::leanh::lean_dec(v_a_2312_);
    crate::leanh::lean_dec_ref(v_a_2311_);
    crate::leanh::lean_dec(v_a_2310_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda(
    mut v_e_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
    mut v_a_2325_: *mut crate::leanh::LeanObject,
    mut v_a_2326_: *mut crate::leanh::LeanObject,
    mut v_a_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lean_Meta_Sym_Simp_simpLambda___closed__0;
    v___x_2334_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(
        v___x_2333_,
        v_e_2322_,
        v_a_2323_,
        v_a_2324_,
        v_a_2325_,
        v_a_2326_,
        v_a_2327_,
        v_a_2328_,
        v_a_2329_,
        v_a_2330_,
        v_a_2331_,
    );
    return v___x_2334_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpLambda___boxed(
    mut v_e_2335_: *mut crate::leanh::LeanObject,
    mut v_a_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_a_2341_: *mut crate::leanh::LeanObject,
    mut v_a_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ = l_Lean_Meta_Sym_Simp_simpLambda(
        v_e_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_,
        v_a_2343_, v_a_2344_,
    );
    crate::leanh::lean_dec(v_a_2344_);
    crate::leanh::lean_dec_ref(v_a_2343_);
    crate::leanh::lean_dec(v_a_2342_);
    crate::leanh::lean_dec_ref(v_a_2341_);
    crate::leanh::lean_dec(v_a_2340_);
    crate::leanh::lean_dec_ref(v_a_2339_);
    crate::leanh::lean_dec(v_a_2338_);
    crate::leanh::lean_dec_ref(v_a_2337_);
    crate::leanh::lean_dec(v_a_2336_);
    return v_res_2346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Lambda(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Lambda(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Lambda(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
}
