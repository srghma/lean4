// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Main
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.DSimp.DSimproc Lean.Meta.Sym.DSimp.App Lean.Meta.Sym.DSimp.Lambda Lean.Meta.Sym.DSimp.Forall Lean.Meta.Sym.DSimp.Let Lean.Meta.Sym.AlphaShareBuilder
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_mdata___override;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::App::{
    initialize_Lean_Meta_Sym_DSimp_App, l_Lean_Meta_Sym_DSimp_dsimpAppArgs,
    runtime_initialize_Lean_Meta_Sym_DSimp_App,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimproc::{
    initialize_Lean_Meta_Sym_DSimp_DSimproc, runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::Forall::{
    initialize_Lean_Meta_Sym_DSimp_Forall, l_Lean_Meta_Sym_DSimp_dsimpForall,
    runtime_initialize_Lean_Meta_Sym_DSimp_Forall,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::Lambda::{
    initialize_Lean_Meta_Sym_DSimp_Lambda, l_Lean_Meta_Sym_DSimp_dsimpLambda,
    runtime_initialize_Lean_Meta_Sym_DSimp_Lambda,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::Let::{
    initialize_Lean_Meta_Sym_DSimp_Let, l_Lean_Meta_Sym_DSimp_dsimpLet,
    runtime_initialize_Lean_Meta_Sym_DSimp_Let,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
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
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Sym::DSimp::DSimpM::lean_sym_dsimp;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value: crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 101, 114, 110, 101, 108, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 101, 114, 109, 32, 100, 117, 114, 105, 110, 103, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [10, 112, 114, 101, 45, 112, 114, 111, 99, 101, 115, 115, 32, 97, 110, 100, 32, 102, 111, 108, 100, 32, 116, 104, 101, 109, 32, 97, 115, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [96, 100, 115, 105, 109, 112, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 115, 116, 101, 112, 115, 32, 101, 120, 99, 101, 101, 100, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(
    mut v_d_851_: *mut crate::leanh::LeanObject,
    mut v_e_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
    mut v___y_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_865_: u8 = 0;
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_864_ = lean_st_ref_get(v___y_854_);
                v_debug_865_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_864_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_864_);
                if v_debug_865_ == 0 {
                    v___y_861_ = v___y_854_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_e_852_);
                    v___x_866_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_e_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_,
                        v___y_858_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_866_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_866_, 1);
                        v___y_861_ = v___y_854_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_852_);
                        crate::leanh::lean_dec(v_d_851_);
                        v_a_867_ = crate::leanh::lean_ctor_get(v___x_866_, 0);
                        v_isSharedCheck_874_ = (!crate::leanh::lean_is_exclusive(v___x_866_)) as u8;
                        if v_isSharedCheck_874_ == 0 {
                            v___x_869_ = v___x_866_;
                            v_isShared_870_ = v_isSharedCheck_874_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_867_);
                            crate::leanh::lean_dec(v___x_866_);
                            v___x_869_ = crate::leanh::lean_box(0);
                            v_isShared_870_ = v_isSharedCheck_874_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_862_ = l_Lean_Expr_mdata___override(v_d_851_, v_e_852_);
                v___x_863_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_862_, v___y_861_);
                return v___x_863_;
            }
            2 => {
                if v_isShared_870_ == 0 {
                    v___x_872_ = v___x_869_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg___boxed(
    mut v_d_875_: *mut crate::leanh::LeanObject,
    mut v_e_876_: *mut crate::leanh::LeanObject,
    mut v___y_877_: *mut crate::leanh::LeanObject,
    mut v___y_878_: *mut crate::leanh::LeanObject,
    mut v___y_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_875_, v_e_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
    crate::leanh::lean_dec(v___y_882_);
    crate::leanh::lean_dec_ref(v___y_881_);
    crate::leanh::lean_dec(v___y_880_);
    crate::leanh::lean_dec_ref(v___y_879_);
    crate::leanh::lean_dec(v___y_878_);
    crate::leanh::lean_dec_ref(v___y_877_);
    return v_res_884_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(
    mut v_d_885_: *mut crate::leanh::LeanObject,
    mut v_e_886_: *mut crate::leanh::LeanObject,
    mut v___y_887_: *mut crate::leanh::LeanObject,
    mut v___y_888_: *mut crate::leanh::LeanObject,
    mut v___y_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
    mut v___y_891_: *mut crate::leanh::LeanObject,
    mut v___y_892_: *mut crate::leanh::LeanObject,
    mut v___y_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_885_, v_e_886_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
    return v___x_897_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(
    mut v_d_898_: *mut crate::leanh::LeanObject,
    mut v_e_899_: *mut crate::leanh::LeanObject,
    mut v___y_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v___y_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
    mut v___y_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(v_d_898_, v_e_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
    crate::leanh::lean_dec(v___y_908_);
    crate::leanh::lean_dec_ref(v___y_907_);
    crate::leanh::lean_dec(v___y_906_);
    crate::leanh::lean_dec_ref(v___y_905_);
    crate::leanh::lean_dec(v___y_904_);
    crate::leanh::lean_dec_ref(v___y_903_);
    crate::leanh::lean_dec(v___y_902_);
    crate::leanh::lean_dec(v___y_901_);
    crate::leanh::lean_dec(v___y_900_);
    return v_res_910_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(
    mut v_msgData_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = lean_st_ref_get(v___y_915_);
    v_env_918_ = crate::leanh::lean_ctor_get(v___x_917_, 0);
    crate::leanh::lean_inc_ref(v_env_918_);
    crate::leanh::lean_dec(v___x_917_);
    v___x_919_ = lean_st_ref_get(v___y_913_);
    v_mctx_920_ = crate::leanh::lean_ctor_get(v___x_919_, 0);
    crate::leanh::lean_inc_ref(v_mctx_920_);
    crate::leanh::lean_dec(v___x_919_);
    v_lctx_921_ = crate::leanh::lean_ctor_get(v___y_912_, 2);
    v_options_922_ = crate::leanh::lean_ctor_get(v___y_914_, 2);
    crate::leanh::lean_inc_ref(v_options_922_);
    crate::leanh::lean_inc_ref(v_lctx_921_);
    v___x_923_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_923_, 0, v_env_918_);
    crate::leanh::lean_ctor_set(v___x_923_, 1, v_mctx_920_);
    crate::leanh::lean_ctor_set(v___x_923_, 2, v_lctx_921_);
    crate::leanh::lean_ctor_set(v___x_923_, 3, v_options_922_);
    v___x_924_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_923_);
    crate::leanh::lean_ctor_set(v___x_924_, 1, v_msgData_911_);
    v___x_925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_924_);
    return v___x_925_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(
    mut v_msgData_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_932_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
    crate::leanh::lean_dec(v___y_930_);
    crate::leanh::lean_dec_ref(v___y_929_);
    crate::leanh::lean_dec(v___y_928_);
    crate::leanh::lean_dec_ref(v___y_927_);
    return v_res_932_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(
    mut v_msg_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
    mut v___y_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_939_ = crate::leanh::lean_ctor_get(v___y_936_, 5);
                v___x_940_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
                v_a_941_ = crate::leanh::lean_ctor_get(v___x_940_, 0);
                v_isSharedCheck_949_ = (!crate::leanh::lean_is_exclusive(v___x_940_)) as u8;
                if v_isSharedCheck_949_ == 0 {
                    v___x_943_ = v___x_940_;
                    v_isShared_944_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_941_);
                    crate::leanh::lean_dec(v___x_940_);
                    v___x_943_ = crate::leanh::lean_box(0);
                    v_isShared_944_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_939_);
                v___x_945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_945_, 0, v_ref_939_);
                crate::leanh::lean_ctor_set(v___x_945_, 1, v_a_941_);
                if v_isShared_944_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_943_, 1);
                    crate::leanh::lean_ctor_set(v___x_943_, 0, v___x_945_);
                    v___x_947_ = v___x_943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
                    v___x_947_ = v_reuseFailAlloc_948_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(
    mut v_msg_950_: *mut crate::leanh::LeanObject,
    mut v___y_951_: *mut crate::leanh::LeanObject,
    mut v___y_952_: *mut crate::leanh::LeanObject,
    mut v___y_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
    crate::leanh::lean_dec(v___y_954_);
    crate::leanh::lean_dec_ref(v___y_953_);
    crate::leanh::lean_dec(v___y_952_);
    crate::leanh::lean_dec_ref(v___y_951_);
    return v_res_956_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1;
    v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
    return v___x_961_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3;
    v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
    return v___x_964_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(
    mut v_e_965_: *mut crate::leanh::LeanObject,
    mut v_a_966_: *mut crate::leanh::LeanObject,
    mut v_a_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
    mut v_a_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: u8 = 0;
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_965_) {
                5 => {
                    v___x_981_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(
                        v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_,
                        v_a_972_, v_a_973_, v_a_974_,
                    );
                    return v___x_981_;
                }
                6 => {
                    v___x_982_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(
                        v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_,
                        v_a_972_, v_a_973_, v_a_974_,
                    );
                    return v___x_982_;
                }
                7 => {
                    v___x_983_ = l_Lean_Meta_Sym_DSimp_dsimpForall(
                        v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_,
                        v_a_972_, v_a_973_, v_a_974_,
                    );
                    return v___x_983_;
                }
                8 => {
                    v___x_984_ = l_Lean_Meta_Sym_DSimp_dsimpLet(
                        v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_,
                        v_a_972_, v_a_973_, v_a_974_,
                    );
                    return v___x_984_;
                }
                10 => {
                    v_data_985_ = crate::leanh::lean_ctor_get(v_e_965_, 0);
                    v_expr_986_ = crate::leanh::lean_ctor_get(v_e_965_, 1);
                    crate::leanh::lean_inc(v_a_974_);
                    crate::leanh::lean_inc_ref(v_a_973_);
                    crate::leanh::lean_inc(v_a_972_);
                    crate::leanh::lean_inc_ref(v_a_971_);
                    crate::leanh::lean_inc(v_a_970_);
                    crate::leanh::lean_inc_ref(v_a_969_);
                    crate::leanh::lean_inc(v_a_968_);
                    crate::leanh::lean_inc(v_a_967_);
                    crate::leanh::lean_inc(v_a_966_);
                    crate::leanh::lean_inc_ref(v_expr_986_);
                    v___x_987_ = lean_sym_dsimp(
                        v_expr_986_,
                        v_a_966_,
                        v_a_967_,
                        v_a_968_,
                        v_a_969_,
                        v_a_970_,
                        v_a_971_,
                        v_a_972_,
                        v_a_973_,
                        v_a_974_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_987_) == 0 {
                        v_a_988_ = crate::leanh::lean_ctor_get(v___x_987_, 0);
                        v_isSharedCheck_1008_ =
                            (!crate::leanh::lean_is_exclusive(v___x_987_)) as u8;
                        if v_isSharedCheck_1008_ == 0 {
                            v___x_990_ = v___x_987_;
                            v_isShared_991_ = v_isSharedCheck_1008_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_988_);
                            crate::leanh::lean_dec(v___x_987_);
                            v___x_990_ = crate::leanh::lean_box(0);
                            v_isShared_991_ = v_isSharedCheck_1008_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_965_, 2);
                        return v___x_987_;
                    }
                }
                11 => {
                    v___x_1009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once), _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2);
                    v___x_1010_ = l_Lean_indentExpr(v_e_965_);
                    v___x_1011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1011_, 0, v___x_1009_);
                    crate::leanh::lean_ctor_set(v___x_1011_, 1, v___x_1010_);
                    v___x_1012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once), _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4);
                    v___x_1013_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1011_);
                    crate::leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
                    v___x_1014_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_1013_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
                    return v___x_1014_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_965_);
                    v___x_1015_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0;
                    v___x_1016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
                    return v___x_1016_;
                }
            },
            1 => {
                v___x_978_ = 0;
                v___x_979_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_979_, 0, v_a_977_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_979_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_978_,
                );
                v___x_980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_980_, 0, v___x_979_);
                return v___x_980_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_988_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_988_, 0);
                    crate::leanh::lean_dec_ref_known(v_e_965_, 2);
                    v___x_992_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0;
                    if v_isShared_991_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_990_, 0, v___x_992_);
                        v___x_994_ = v___x_990_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
                        v___x_994_ = v_reuseFailAlloc_995_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_990_);
                    v_e_x27_996_ = crate::leanh::lean_ctor_get(v_a_988_, 0);
                    crate::leanh::lean_inc_ref(v_e_x27_996_);
                    crate::leanh::lean_dec_ref_known(v_a_988_, 1);
                    v___x_997_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_expr_986_,
                            v_e_x27_996_,
                        );
                    if v___x_997_ == 0 {
                        crate::leanh::lean_inc(v_data_985_);
                        crate::leanh::lean_dec_ref_known(v_e_965_, 2);
                        v___x_998_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_data_985_, v_e_x27_996_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
                        if crate::leanh::lean_obj_tag(v___x_998_) == 0 {
                            v_a_999_ = crate::leanh::lean_ctor_get(v___x_998_, 0);
                            crate::leanh::lean_inc(v_a_999_);
                            crate::leanh::lean_dec_ref_known(v___x_998_, 1);
                            v_a_977_ = v_a_999_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1000_ = crate::leanh::lean_ctor_get(v___x_998_, 0);
                            v_isSharedCheck_1007_ =
                                (!crate::leanh::lean_is_exclusive(v___x_998_)) as u8;
                            if v_isSharedCheck_1007_ == 0 {
                                v___x_1002_ = v___x_998_;
                                v_isShared_1003_ = v_isSharedCheck_1007_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1000_);
                                crate::leanh::lean_dec(v___x_998_);
                                v___x_1002_ = crate::leanh::lean_box(0);
                                v_isShared_1003_ = v_isSharedCheck_1007_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_x27_996_);
                        v_a_977_ = v_e_965_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_994_;
            }
            4 => {
                if v_isShared_1003_ == 0 {
                    v___x_1005_ = v___x_1002_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
                    v___x_1005_ = v_reuseFailAlloc_1006_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(
    mut v_e_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
    mut v_a_1026_: *mut crate::leanh::LeanObject,
    mut v_a_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(
        v_e_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_,
        v_a_1025_, v_a_1026_,
    );
    crate::leanh::lean_dec(v_a_1026_);
    crate::leanh::lean_dec_ref(v_a_1025_);
    crate::leanh::lean_dec(v_a_1024_);
    crate::leanh::lean_dec_ref(v_a_1023_);
    crate::leanh::lean_dec(v_a_1022_);
    crate::leanh::lean_dec_ref(v_a_1021_);
    crate::leanh::lean_dec(v_a_1020_);
    crate::leanh::lean_dec(v_a_1019_);
    crate::leanh::lean_dec(v_a_1018_);
    return v_res_1028_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(
    mut v_00_u03b1_1029_: *mut crate::leanh::LeanObject,
    mut v_msg_1030_: *mut crate::leanh::LeanObject,
    mut v___y_1031_: *mut crate::leanh::LeanObject,
    mut v___y_1032_: *mut crate::leanh::LeanObject,
    mut v___y_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1041_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_1030_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
    return v___x_1041_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(
    mut v_00_u03b1_1042_: *mut crate::leanh::LeanObject,
    mut v_msg_1043_: *mut crate::leanh::LeanObject,
    mut v___y_1044_: *mut crate::leanh::LeanObject,
    mut v___y_1045_: *mut crate::leanh::LeanObject,
    mut v___y_1046_: *mut crate::leanh::LeanObject,
    mut v___y_1047_: *mut crate::leanh::LeanObject,
    mut v___y_1048_: *mut crate::leanh::LeanObject,
    mut v___y_1049_: *mut crate::leanh::LeanObject,
    mut v___y_1050_: *mut crate::leanh::LeanObject,
    mut v___y_1051_: *mut crate::leanh::LeanObject,
    mut v___y_1052_: *mut crate::leanh::LeanObject,
    mut v___y_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(v_00_u03b1_1042_, v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
    crate::leanh::lean_dec(v___y_1052_);
    crate::leanh::lean_dec_ref(v___y_1051_);
    crate::leanh::lean_dec(v___y_1050_);
    crate::leanh::lean_dec_ref(v___y_1049_);
    crate::leanh::lean_dec(v___y_1048_);
    crate::leanh::lean_dec_ref(v___y_1047_);
    crate::leanh::lean_dec(v___y_1046_);
    crate::leanh::lean_dec(v___y_1045_);
    crate::leanh::lean_dec(v___y_1044_);
    return v_res_1054_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(
    mut v_e_1057_: *mut crate::leanh::LeanObject,
    mut v_r_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___f_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1061_ = lean_st_ref_take(v_a_1059_);
                v_numSteps_1062_ = crate::leanh::lean_ctor_get(v___x_1061_, 0);
                v_cache_1063_ = crate::leanh::lean_ctor_get(v___x_1061_, 1);
                v_isSharedCheck_1075_ = (!crate::leanh::lean_is_exclusive(v___x_1061_)) as u8;
                if v_isSharedCheck_1075_ == 0 {
                    v___x_1065_ = v___x_1061_;
                    v_isShared_1066_ = v_isSharedCheck_1075_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1063_);
                    crate::leanh::lean_inc(v_numSteps_1062_);
                    crate::leanh::lean_dec(v___x_1061_);
                    v___x_1065_ = crate::leanh::lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1067_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0;
                v___f_1068_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1;
                crate::leanh::lean_inc_ref(v_r_1058_);
                v___x_1069_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1067_,
                    v___f_1068_,
                    v_cache_1063_,
                    v_e_1057_,
                    v_r_1058_,
                );
                if v_isShared_1066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1065_, 1, v___x_1069_);
                    v___x_1071_ = v___x_1065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_numSteps_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1072_ = lean_st_ref_set(v_a_1059_, v___x_1071_);
                v___x_1073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1073_, 0, v_r_1058_);
                return v___x_1073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(
    mut v_e_1076_: *mut crate::leanh::LeanObject,
    mut v_r_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1080_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(
        v_e_1076_, v_r_1077_, v_a_1078_,
    );
    crate::leanh::lean_dec(v_a_1078_);
    return v_res_1080_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(
    mut v_e_1081_: *mut crate::leanh::LeanObject,
    mut v_r_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___f_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = lean_st_ref_take(v_a_1085_);
                v_numSteps_1094_ = crate::leanh::lean_ctor_get(v___x_1093_, 0);
                v_cache_1095_ = crate::leanh::lean_ctor_get(v___x_1093_, 1);
                v_isSharedCheck_1107_ = (!crate::leanh::lean_is_exclusive(v___x_1093_)) as u8;
                if v_isSharedCheck_1107_ == 0 {
                    v___x_1097_ = v___x_1093_;
                    v_isShared_1098_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1095_);
                    crate::leanh::lean_inc(v_numSteps_1094_);
                    crate::leanh::lean_dec(v___x_1093_);
                    v___x_1097_ = crate::leanh::lean_box(0);
                    v_isShared_1098_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1099_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0;
                v___f_1100_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1;
                crate::leanh::lean_inc_ref(v_r_1082_);
                v___x_1101_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1099_,
                    v___f_1100_,
                    v_cache_1095_,
                    v_e_1081_,
                    v_r_1082_,
                );
                if v_isShared_1098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1097_, 1, v___x_1101_);
                    v___x_1103_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_numSteps_1094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1101_);
                    v___x_1103_ = v_reuseFailAlloc_1106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1104_ = lean_st_ref_set(v_a_1085_, v___x_1103_);
                v___x_1105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1105_, 0, v_r_1082_);
                return v___x_1105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(
    mut v_e_1108_: *mut crate::leanh::LeanObject,
    mut v_r_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(
        v_e_1108_, v_r_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_,
        v_a_1116_, v_a_1117_, v_a_1118_,
    );
    crate::leanh::lean_dec(v_a_1118_);
    crate::leanh::lean_dec_ref(v_a_1117_);
    crate::leanh::lean_dec(v_a_1116_);
    crate::leanh::lean_dec_ref(v_a_1115_);
    crate::leanh::lean_dec(v_a_1114_);
    crate::leanh::lean_dec_ref(v_a_1113_);
    crate::leanh::lean_dec(v_a_1112_);
    crate::leanh::lean_dec(v_a_1111_);
    crate::leanh::lean_dec(v_a_1110_);
    return v_res_1120_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1127_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3);
    v___x_1129_ = l_Lean_MessageData_ofFormat(v___x_1128_);
    return v___x_1129_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4);
    v___x_1131_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2;
    v___x_1132_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1132_, 0, v___x_1131_);
    crate::leanh::lean_ctor_set(v___x_1132_, 1, v___x_1130_);
    return v___x_1132_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(
    mut v_ref_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5);
    v___x_1136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1136_, 0, v_ref_1133_);
    crate::leanh::lean_ctor_set(v___x_1136_, 1, v___x_1135_);
    v___x_1137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(
    mut v_ref_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_1138_);
    return v_res_1140_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(
    mut v_00_u03b1_1141_: *mut crate::leanh::LeanObject,
    mut v_ref_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_1142_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(
    mut v_00_u03b1_1154_: *mut crate::leanh::LeanObject,
    mut v_ref_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
    mut v___y_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(v_00_u03b1_1154_, v_ref_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
    crate::leanh::lean_dec(v___y_1164_);
    crate::leanh::lean_dec_ref(v___y_1163_);
    crate::leanh::lean_dec(v___y_1162_);
    crate::leanh::lean_dec_ref(v___y_1161_);
    crate::leanh::lean_dec(v___y_1160_);
    crate::leanh::lean_dec_ref(v___y_1159_);
    crate::leanh::lean_dec(v___y_1158_);
    crate::leanh::lean_dec(v___y_1157_);
    crate::leanh::lean_dec(v___y_1156_);
    return v_res_1166_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(
    mut v_x_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_post_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_post_1179_ = crate::leanh::lean_ctor_get(v___y_1169_, 1);
    crate::leanh::lean_inc_ref(v_post_1179_);
    crate::leanh::lean_inc(v___y_1177_);
    crate::leanh::lean_inc_ref(v___y_1176_);
    crate::leanh::lean_inc(v___y_1175_);
    crate::leanh::lean_inc_ref(v___y_1174_);
    crate::leanh::lean_inc(v___y_1173_);
    crate::leanh::lean_inc_ref(v___y_1172_);
    crate::leanh::lean_inc(v___y_1171_);
    crate::leanh::lean_inc(v___y_1170_);
    crate::leanh::lean_inc(v___y_1169_);
    v___x_1180_ = crate::leanh::lean_apply_11(
        v_post_1179_,
        v___y_1168_,
        v___y_1169_,
        v___y_1170_,
        v___y_1171_,
        v___y_1172_,
        v___y_1173_,
        v___y_1174_,
        v___y_1175_,
        v___y_1176_,
        v___y_1177_,
        crate::leanh::lean_box(0),
    );
    return v___x_1180_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(
    mut v_x_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(
        v_x_1181_,
        v___y_1182_,
        v___y_1183_,
        v___y_1184_,
        v___y_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
        v___y_1189_,
        v___y_1190_,
        v___y_1191_,
    );
    crate::leanh::lean_dec(v___y_1191_);
    crate::leanh::lean_dec_ref(v___y_1190_);
    crate::leanh::lean_dec(v___y_1189_);
    crate::leanh::lean_dec_ref(v___y_1188_);
    crate::leanh::lean_dec(v___y_1187_);
    crate::leanh::lean_dec_ref(v___y_1186_);
    crate::leanh::lean_dec(v___y_1185_);
    crate::leanh::lean_dec(v___y_1184_);
    crate::leanh::lean_dec(v___y_1183_);
    return v_res_1193_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_1194_: *mut crate::leanh::LeanObject,
    mut v_x_1195_: *mut crate::leanh::LeanObject,
    mut v_x_1196_: *mut crate::leanh::LeanObject,
    mut v_x_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1198_ = crate::leanh::lean_ctor_get(v_x_1194_, 0);
                v_vs_1199_ = crate::leanh::lean_ctor_get(v_x_1194_, 1);
                v_isSharedCheck_1223_ = (!crate::leanh::lean_is_exclusive(v_x_1194_)) as u8;
                if v_isSharedCheck_1223_ == 0 {
                    v___x_1201_ = v_x_1194_;
                    v_isShared_1202_ = v_isSharedCheck_1223_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1199_);
                    crate::leanh::lean_inc(v_ks_1198_);
                    crate::leanh::lean_dec(v_x_1194_);
                    v___x_1201_ = crate::leanh::lean_box(0);
                    v_isShared_1202_ = v_isSharedCheck_1223_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1203_ = lean_array_get_size(v_ks_1198_);
                v___x_1204_ = lean_nat_dec_lt(v_x_1195_, v___x_1203_);
                if v___x_1204_ == 0 {
                    crate::leanh::lean_dec(v_x_1195_);
                    v___x_1205_ = lean_array_push(v_ks_1198_, v_x_1196_);
                    v___x_1206_ = lean_array_push(v_vs_1199_, v_x_1197_);
                    if v_isShared_1202_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1201_, 1, v___x_1206_);
                        crate::leanh::lean_ctor_set(v___x_1201_, 0, v___x_1205_);
                        v___x_1208_ = v___x_1201_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1209_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1205_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
                        v___x_1208_ = v_reuseFailAlloc_1209_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1210_ = lean_array_fget_borrowed(v_ks_1198_, v_x_1195_);
                    v___x_1211_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1196_,
                            v_k_x27_1210_,
                        );
                    if v___x_1211_ == 0 {
                        if v_isShared_1202_ == 0 {
                            v___x_1213_ = v___x_1201_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1217_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_ks_1198_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_vs_1199_);
                            v___x_1213_ = v_reuseFailAlloc_1217_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1218_ = lean_array_fset(v_ks_1198_, v_x_1195_, v_x_1196_);
                        v___x_1219_ = lean_array_fset(v_vs_1199_, v_x_1195_, v_x_1197_);
                        crate::leanh::lean_dec(v_x_1195_);
                        if v_isShared_1202_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1201_, 1, v___x_1219_);
                            crate::leanh::lean_ctor_set(v___x_1201_, 0, v___x_1218_);
                            v___x_1221_ = v___x_1201_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1222_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
                            v___x_1221_ = v_reuseFailAlloc_1222_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1208_;
            }
            3 => {
                v___x_1214_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1215_ = lean_nat_add(v_x_1195_, v___x_1214_);
                crate::leanh::lean_dec(v_x_1195_);
                v_x_1194_ = v___x_1213_;
                v_x_1195_ = v___x_1215_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(
    mut v_n_1224_: *mut crate::leanh::LeanObject,
    mut v_k_1225_: *mut crate::leanh::LeanObject,
    mut v_v_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1228_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1224_, v___x_1227_, v_k_1225_, v_v_1226_);
    return v___x_1228_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1229_: usize = 0;
    let mut v___x_1230_: usize = 0;
    let mut v___x_1231_: usize = 0;
    v___x_1229_ = 5usize;
    v___x_1230_ = 1usize;
    v___x_1231_ = lean_usize_shift_left(v___x_1230_, v___x_1229_);
    return v___x_1231_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1232_: usize = 0;
    let mut v___x_1233_: usize = 0;
    let mut v___x_1234_: usize = 0;
    v___x_1232_ = 1usize;
    v___x_1233_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0);
    v___x_1234_ = lean_usize_sub(v___x_1233_, v___x_1232_);
    return v___x_1234_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1235_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(
    mut v_x_1236_: *mut crate::leanh::LeanObject,
    mut v_x_1237_: usize,
    mut v_x_1238_: usize,
    mut v_x_1239_: *mut crate::leanh::LeanObject,
    mut v_x_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v_j_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v_v_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_node_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1277_: usize = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1283_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1296_: u8 = 0;
    let mut v_ks_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v_reuseFailAlloc_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1236_) == 0 {
                    v_es_1241_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                    v___x_1242_ = 5usize;
                    v___x_1243_ = 1usize;
                    v___x_1244_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1);
                    v___x_1245_ = lean_usize_land(v_x_1237_, v___x_1244_);
                    v_j_1246_ = lean_usize_to_nat(v___x_1245_);
                    v___x_1247_ = lean_array_get_size(v_es_1241_);
                    v___x_1248_ = lean_nat_dec_lt(v_j_1246_, v___x_1247_);
                    if v___x_1248_ == 0 {
                        crate::leanh::lean_dec(v_j_1246_);
                        crate::leanh::lean_dec(v_x_1240_);
                        crate::leanh::lean_dec_ref(v_x_1239_);
                        return v_x_1236_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1241_);
                        v_isSharedCheck_1285_ = (!crate::leanh::lean_is_exclusive(v_x_1236_)) as u8;
                        if v_isSharedCheck_1285_ == 0 {
                            v_unused_1286_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                            crate::leanh::lean_dec(v_unused_1286_);
                            v___x_1250_ = v_x_1236_;
                            v_isShared_1251_ = v_isSharedCheck_1285_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1236_);
                            v___x_1250_ = crate::leanh::lean_box(0);
                            v_isShared_1251_ = v_isSharedCheck_1285_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1287_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                    v_vs_1288_ = crate::leanh::lean_ctor_get(v_x_1236_, 1);
                    v_isSharedCheck_1308_ = (!crate::leanh::lean_is_exclusive(v_x_1236_)) as u8;
                    if v_isSharedCheck_1308_ == 0 {
                        v___x_1290_ = v_x_1236_;
                        v_isShared_1291_ = v_isSharedCheck_1308_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1288_);
                        crate::leanh::lean_inc(v_ks_1287_);
                        crate::leanh::lean_dec(v_x_1236_);
                        v___x_1290_ = crate::leanh::lean_box(0);
                        v_isShared_1291_ = v_isSharedCheck_1308_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1252_ = lean_array_fget(v_es_1241_, v_j_1246_);
                v___x_1253_ = crate::leanh::lean_box(0);
                v_xs_x27_1254_ = lean_array_fset(v_es_1241_, v_j_1246_, v___x_1253_);
                match crate::leanh::lean_obj_tag(v_v_1252_) {
                    0 => {
                        v_key_1261_ = crate::leanh::lean_ctor_get(v_v_1252_, 0);
                        v_val_1262_ = crate::leanh::lean_ctor_get(v_v_1252_, 1);
                        v_isSharedCheck_1272_ = (!crate::leanh::lean_is_exclusive(v_v_1252_)) as u8;
                        if v_isSharedCheck_1272_ == 0 {
                            v___x_1264_ = v_v_1252_;
                            v_isShared_1265_ = v_isSharedCheck_1272_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1262_);
                            crate::leanh::lean_inc(v_key_1261_);
                            crate::leanh::lean_dec(v_v_1252_);
                            v___x_1264_ = crate::leanh::lean_box(0);
                            v_isShared_1265_ = v_isSharedCheck_1272_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1273_ = crate::leanh::lean_ctor_get(v_v_1252_, 0);
                        v_isSharedCheck_1283_ = (!crate::leanh::lean_is_exclusive(v_v_1252_)) as u8;
                        if v_isSharedCheck_1283_ == 0 {
                            v___x_1275_ = v_v_1252_;
                            v_isShared_1276_ = v_isSharedCheck_1283_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1273_);
                            crate::leanh::lean_dec(v_v_1252_);
                            v___x_1275_ = crate::leanh::lean_box(0);
                            v_isShared_1276_ = v_isSharedCheck_1283_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1284_, 0, v_x_1239_);
                        crate::leanh::lean_ctor_set(v___x_1284_, 1, v_x_1240_);
                        v___y_1256_ = v___x_1284_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1257_ = lean_array_fset(v_xs_x27_1254_, v_j_1246_, v___y_1256_);
                crate::leanh::lean_dec(v_j_1246_);
                if v_isShared_1251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1257_);
                    v___x_1259_ = v___x_1250_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
                    v___x_1259_ = v_reuseFailAlloc_1260_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1259_;
            }
            4 => {
                v___x_1266_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1239_,
                        v_key_1261_,
                    );
                if v___x_1266_ == 0 {
                    crate::leanh::lean_del_object(v___x_1264_);
                    v___x_1267_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1261_,
                        v_val_1262_,
                        v_x_1239_,
                        v_x_1240_,
                    );
                    v___x_1268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
                    v___y_1256_ = v___x_1268_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1262_);
                    crate::leanh::lean_dec(v_key_1261_);
                    if v_isShared_1265_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1264_, 1, v_x_1240_);
                        crate::leanh::lean_ctor_set(v___x_1264_, 0, v_x_1239_);
                        v___x_1270_ = v___x_1264_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_x_1239_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_x_1240_);
                        v___x_1270_ = v_reuseFailAlloc_1271_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1256_ = v___x_1270_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1277_ = lean_usize_shift_right(v_x_1237_, v___x_1242_);
                v___x_1278_ = lean_usize_add(v_x_1238_, v___x_1243_);
                v___x_1279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_node_1273_, v___x_1277_, v___x_1278_, v_x_1239_, v_x_1240_);
                if v_isShared_1276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1275_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
                    v___x_1281_ = v_reuseFailAlloc_1282_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1256_ = v___x_1281_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1291_ == 0 {
                    v___x_1293_ = v___x_1290_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1307_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_ks_1287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_vs_1288_);
                    v___x_1293_ = v_reuseFailAlloc_1307_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1294_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v___x_1293_, v_x_1239_, v_x_1240_);
                v___x_1302_ = 7usize;
                v___x_1303_ = lean_usize_dec_le(v___x_1302_, v_x_1238_);
                if v___x_1303_ == 0 {
                    v___x_1304_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1294_);
                    v___x_1305_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1306_ = lean_nat_dec_lt(v___x_1304_, v___x_1305_);
                    crate::leanh::lean_dec(v___x_1304_);
                    v___y_1296_ = v___x_1306_;
                    state = 10;
                    continue;
                } else {
                    v___y_1296_ = v___x_1303_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1296_ == 0 {
                    v_ks_1297_ = crate::leanh::lean_ctor_get(v_newNode_1294_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1297_);
                    v_vs_1298_ = crate::leanh::lean_ctor_get(v_newNode_1294_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1298_);
                    crate::leanh::lean_dec_ref(v_newNode_1294_);
                    v___x_1299_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1300_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2);
                    v___x_1301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_x_1238_, v_ks_1297_, v_vs_1298_, v___x_1299_, v___x_1300_);
                    crate::leanh::lean_dec_ref(v_vs_1298_);
                    crate::leanh::lean_dec_ref(v_ks_1297_);
                    return v___x_1301_;
                } else {
                    return v_newNode_1294_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(
    mut v_depth_1309_: usize,
    mut v_keys_1310_: *mut crate::leanh::LeanObject,
    mut v_vals_1311_: *mut crate::leanh::LeanObject,
    mut v_i_1312_: *mut crate::leanh::LeanObject,
    mut v_entries_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v_k_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u64 = 0;
    let mut v_h_1319_: usize = 0;
    let mut v___x_1320_: usize = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: usize = 0;
    let mut v___x_1323_: usize = 0;
    let mut v___x_1324_: usize = 0;
    let mut v_h_1325_: usize = 0;
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1314_ = lean_array_get_size(v_keys_1310_);
                v___x_1315_ = lean_nat_dec_lt(v_i_1312_, v___x_1314_);
                if v___x_1315_ == 0 {
                    crate::leanh::lean_dec(v_i_1312_);
                    return v_entries_1313_;
                } else {
                    v_k_1316_ = lean_array_fget_borrowed(v_keys_1310_, v_i_1312_);
                    v_v_1317_ = lean_array_fget_borrowed(v_vals_1311_, v_i_1312_);
                    v___x_1318_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1316_);
                    v_h_1319_ = lean_uint64_to_usize(v___x_1318_);
                    v___x_1320_ = 5usize;
                    v___x_1321_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1322_ = 1usize;
                    v___x_1323_ = lean_usize_sub(v_depth_1309_, v___x_1322_);
                    v___x_1324_ = lean_usize_mul(v___x_1320_, v___x_1323_);
                    v_h_1325_ = lean_usize_shift_right(v_h_1319_, v___x_1324_);
                    v___x_1326_ = lean_nat_add(v_i_1312_, v___x_1321_);
                    crate::leanh::lean_dec(v_i_1312_);
                    crate::leanh::lean_inc(v_v_1317_);
                    crate::leanh::lean_inc(v_k_1316_);
                    v___x_1327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_entries_1313_, v_h_1325_, v_depth_1309_, v_k_1316_, v_v_1317_);
                    v_i_1312_ = v___x_1326_;
                    v_entries_1313_ = v___x_1327_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_depth_1329_: *mut crate::leanh::LeanObject,
    mut v_keys_1330_: *mut crate::leanh::LeanObject,
    mut v_vals_1331_: *mut crate::leanh::LeanObject,
    mut v_i_1332_: *mut crate::leanh::LeanObject,
    mut v_entries_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1334_: usize = 0;
    let mut v_res_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1334_ = crate::leanh::lean_unbox_usize(v_depth_1329_);
    crate::leanh::lean_dec(v_depth_1329_);
    v_res_1335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1334_, v_keys_1330_, v_vals_1331_, v_i_1332_, v_entries_1333_);
    crate::leanh::lean_dec_ref(v_vals_1331_);
    crate::leanh::lean_dec_ref(v_keys_1330_);
    return v_res_1335_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(
    mut v_x_1336_: *mut crate::leanh::LeanObject,
    mut v_x_1337_: *mut crate::leanh::LeanObject,
    mut v_x_1338_: *mut crate::leanh::LeanObject,
    mut v_x_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42469__boxed_1341_: usize = 0;
    let mut v_x_42470__boxed_1342_: usize = 0;
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42469__boxed_1341_ = crate::leanh::lean_unbox_usize(v_x_1337_);
    crate::leanh::lean_dec(v_x_1337_);
    v_x_42470__boxed_1342_ = crate::leanh::lean_unbox_usize(v_x_1338_);
    crate::leanh::lean_dec(v_x_1338_);
    v_res_1343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_1336_, v_x_42469__boxed_1341_, v_x_42470__boxed_1342_, v_x_1339_, v_x_1340_);
    return v_res_1343_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(
    mut v_x_1344_: *mut crate::leanh::LeanObject,
    mut v_x_1345_: *mut crate::leanh::LeanObject,
    mut v_x_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: u64 = 0;
    let mut v___x_1348_: usize = 0;
    let mut v___x_1349_: usize = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1345_);
    v___x_1348_ = lean_uint64_to_usize(v___x_1347_);
    v___x_1349_ = 1usize;
    v___x_1350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_1344_, v___x_1348_, v___x_1349_, v_x_1345_, v_x_1346_);
    return v___x_1350_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(
    mut v_keys_1351_: *mut crate::leanh::LeanObject,
    mut v_vals_1352_: *mut crate::leanh::LeanObject,
    mut v_i_1353_: *mut crate::leanh::LeanObject,
    mut v_k_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1355_ = lean_array_get_size(v_keys_1351_);
                v___x_1356_ = lean_nat_dec_lt(v_i_1353_, v___x_1355_);
                if v___x_1356_ == 0 {
                    crate::leanh::lean_dec(v_i_1353_);
                    v___x_1357_ = crate::leanh::lean_box(0);
                    return v___x_1357_;
                } else {
                    v_k_x27_1358_ = lean_array_fget_borrowed(v_keys_1351_, v_i_1353_);
                    v___x_1359_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1354_,
                            v_k_x27_1358_,
                        );
                    if v___x_1359_ == 0 {
                        v___x_1360_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1361_ = lean_nat_add(v_i_1353_, v___x_1360_);
                        crate::leanh::lean_dec(v_i_1353_);
                        v_i_1353_ = v___x_1361_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1363_ = lean_array_fget_borrowed(v_vals_1352_, v_i_1353_);
                        crate::leanh::lean_dec(v_i_1353_);
                        crate::leanh::lean_inc(v___x_1363_);
                        v___x_1364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1363_);
                        return v___x_1364_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_keys_1365_: *mut crate::leanh::LeanObject,
    mut v_vals_1366_: *mut crate::leanh::LeanObject,
    mut v_i_1367_: *mut crate::leanh::LeanObject,
    mut v_k_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1369_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1365_, v_vals_1366_, v_i_1367_, v_k_1368_);
    crate::leanh::lean_dec_ref(v_k_1368_);
    crate::leanh::lean_dec_ref(v_vals_1366_);
    crate::leanh::lean_dec_ref(v_keys_1365_);
    return v_res_1369_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(
    mut v_x_1370_: *mut crate::leanh::LeanObject,
    mut v_x_1371_: usize,
    mut v_x_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: usize = 0;
    let mut v___x_1376_: usize = 0;
    let mut v___x_1377_: usize = 0;
    let mut v_j_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: usize = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1370_) == 0 {
                    v_es_1373_ = crate::leanh::lean_ctor_get(v_x_1370_, 0);
                    v___x_1374_ = crate::leanh::lean_box(2);
                    v___x_1375_ = 5usize;
                    v___x_1376_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1);
                    v___x_1377_ = lean_usize_land(v_x_1371_, v___x_1376_);
                    v_j_1378_ = lean_usize_to_nat(v___x_1377_);
                    v___x_1379_ = lean_array_get_borrowed(v___x_1374_, v_es_1373_, v_j_1378_);
                    crate::leanh::lean_dec(v_j_1378_);
                    match crate::leanh::lean_obj_tag(v___x_1379_) {
                        0 => {
                            v_key_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                            v_val_1381_ = crate::leanh::lean_ctor_get(v___x_1379_, 1);
                            v___x_1382_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1372_, v_key_1380_);
                            if v___x_1382_ == 0 {
                                v___x_1383_ = crate::leanh::lean_box(0);
                                return v___x_1383_;
                            } else {
                                crate::leanh::lean_inc(v_val_1381_);
                                v___x_1384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1384_, 0, v_val_1381_);
                                return v___x_1384_;
                            }
                        }
                        1 => {
                            v_node_1385_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                            v___x_1386_ = lean_usize_shift_right(v_x_1371_, v___x_1375_);
                            v_x_1370_ = v_node_1385_;
                            v_x_1371_ = v___x_1386_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1388_ = crate::leanh::lean_box(0);
                            return v___x_1388_;
                        }
                    }
                } else {
                    v_ks_1389_ = crate::leanh::lean_ctor_get(v_x_1370_, 0);
                    v_vs_1390_ = crate::leanh::lean_ctor_get(v_x_1370_, 1);
                    v___x_1391_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_ks_1389_, v_vs_1390_, v___x_1391_, v_x_1372_);
                    return v___x_1392_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(
    mut v_x_1393_: *mut crate::leanh::LeanObject,
    mut v_x_1394_: *mut crate::leanh::LeanObject,
    mut v_x_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42669__boxed_1396_: usize = 0;
    let mut v_res_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42669__boxed_1396_ = crate::leanh::lean_unbox_usize(v_x_1394_);
    crate::leanh::lean_dec(v_x_1394_);
    v_res_1397_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_1393_, v_x_42669__boxed_1396_, v_x_1395_);
    crate::leanh::lean_dec_ref(v_x_1395_);
    crate::leanh::lean_dec_ref(v_x_1393_);
    return v_res_1397_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(
    mut v_x_1398_: *mut crate::leanh::LeanObject,
    mut v_x_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: u64 = 0;
    let mut v___x_1401_: usize = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1399_);
    v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
    v___x_1402_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_1398_, v___x_1401_, v_x_1399_);
    return v___x_1402_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(
    mut v_x_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_1403_, v_x_1404_);
    crate::leanh::lean_dec_ref(v_x_1404_);
    crate::leanh::lean_dec_ref(v_x_1403_);
    return v_res_1405_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1;
    v___x_1409_ = l_Lean_stringToMessageData(v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn lean_sym_dsimp(
    mut v_e_u2081_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
    mut v_a_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_e_u2082_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1450_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1464_: u8 = 0;
    let mut v___y_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1478_: u8 = 0;
    let mut v_fileName_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1491_: u8 = 0;
    let mut v_cancelTk_x3f_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1493_: u8 = 0;
    let mut v_inheritedTraceOptions_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___y_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1520_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1524_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1526_: u8 = 0;
    let mut v_e_x27_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1533_: u8 = 0;
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1538_: u8 = 0;
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut v_done_1540_: u8 = 0;
    let mut v_e_x27_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v_unused_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: u8 = 0;
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_reuseFailAlloc_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1479_ = crate::leanh::lean_ctor_get(v_a_1418_, 0);
                v_fileMap_1480_ = crate::leanh::lean_ctor_get(v_a_1418_, 1);
                v_options_1481_ = crate::leanh::lean_ctor_get(v_a_1418_, 2);
                v_currRecDepth_1482_ = crate::leanh::lean_ctor_get(v_a_1418_, 3);
                v_maxRecDepth_1483_ = crate::leanh::lean_ctor_get(v_a_1418_, 4);
                v_ref_1484_ = crate::leanh::lean_ctor_get(v_a_1418_, 5);
                v_currNamespace_1485_ = crate::leanh::lean_ctor_get(v_a_1418_, 6);
                v_openDecls_1486_ = crate::leanh::lean_ctor_get(v_a_1418_, 7);
                v_initHeartbeats_1487_ = crate::leanh::lean_ctor_get(v_a_1418_, 8);
                v_maxHeartbeats_1488_ = crate::leanh::lean_ctor_get(v_a_1418_, 9);
                v_quotContext_1489_ = crate::leanh::lean_ctor_get(v_a_1418_, 10);
                v_currMacroScope_1490_ = crate::leanh::lean_ctor_get(v_a_1418_, 11);
                v_diag_1491_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1418_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1492_ = crate::leanh::lean_ctor_get(v_a_1418_, 12);
                v_suppressElabErrors_1493_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1418_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1494_ = crate::leanh::lean_ctor_get(v_a_1418_, 13);
                v_isSharedCheck_1606_ = (!crate::leanh::lean_is_exclusive(v_a_1418_)) as u8;
                if v_isSharedCheck_1606_ == 0 {
                    v___x_1496_ = v_a_1418_;
                    v_isShared_1497_ = v_isSharedCheck_1606_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inheritedTraceOptions_1494_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1492_);
                    crate::leanh::lean_inc(v_currMacroScope_1490_);
                    crate::leanh::lean_inc(v_quotContext_1489_);
                    crate::leanh::lean_inc(v_maxHeartbeats_1488_);
                    crate::leanh::lean_inc(v_initHeartbeats_1487_);
                    crate::leanh::lean_inc(v_openDecls_1486_);
                    crate::leanh::lean_inc(v_currNamespace_1485_);
                    crate::leanh::lean_inc(v_ref_1484_);
                    crate::leanh::lean_inc(v_maxRecDepth_1483_);
                    crate::leanh::lean_inc(v_currRecDepth_1482_);
                    crate::leanh::lean_inc(v_options_1481_);
                    crate::leanh::lean_inc(v_fileMap_1480_);
                    crate::leanh::lean_inc(v_fileName_1479_);
                    crate::leanh::lean_dec(v_a_1418_);
                    v___x_1496_ = crate::leanh::lean_box(0);
                    v_isShared_1497_ = v_isSharedCheck_1606_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_1424_ = lean_st_ref_take(v___y_1423_);
                v_numSteps_1425_ = crate::leanh::lean_ctor_get(v___x_1424_, 0);
                v_cache_1426_ = crate::leanh::lean_ctor_get(v___x_1424_, 1);
                v_isSharedCheck_1436_ = (!crate::leanh::lean_is_exclusive(v___x_1424_)) as u8;
                if v_isSharedCheck_1436_ == 0 {
                    v___x_1428_ = v___x_1424_;
                    v_isShared_1429_ = v_isSharedCheck_1436_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1426_);
                    crate::leanh::lean_inc(v_numSteps_1425_);
                    crate::leanh::lean_dec(v___x_1424_);
                    v___x_1428_ = crate::leanh::lean_box(0);
                    v_isShared_1429_ = v_isSharedCheck_1436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_r_1422_);
                v___x_1430_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_cache_1426_, v_e_u2081_1410_, v_r_1422_);
                if v_isShared_1429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1428_, 1, v___x_1430_);
                    v___x_1432_ = v___x_1428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_numSteps_1425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1430_);
                    v___x_1432_ = v_reuseFailAlloc_1435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1433_ = lean_st_ref_set(v___y_1423_, v___x_1432_);
                crate::leanh::lean_dec(v___y_1423_);
                v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1434_, 0, v_r_1422_);
                return v___x_1434_;
            }
            4 => {
                crate::leanh::lean_inc(v___y_1441_);
                crate::leanh::lean_inc_ref(v_e_u2082_1438_);
                v___x_1448_ = lean_sym_dsimp(
                    v_e_u2082_1438_,
                    v___y_1439_,
                    v___y_1440_,
                    v___y_1441_,
                    v___y_1442_,
                    v___y_1443_,
                    v___y_1444_,
                    v___y_1445_,
                    v___y_1446_,
                    v___y_1447_,
                );
                if crate::leanh::lean_obj_tag(v___x_1448_) == 0 {
                    v_a_1449_ = crate::leanh::lean_ctor_get(v___x_1448_, 0);
                    crate::leanh::lean_inc(v_a_1449_);
                    crate::leanh::lean_dec_ref_known(v___x_1448_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1449_) == 0 {
                        v_done_1450_ = crate::leanh::lean_ctor_get_uint8(v_a_1449_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_a_1449_, 0);
                        v___x_1451_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1451_, 0, v_e_u2082_1438_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1451_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_done_1450_,
                        );
                        v_r_1422_ = v___x_1451_;
                        v___y_1423_ = v___y_1441_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_u2082_1438_);
                        v_r_1422_ = v_a_1449_;
                        v___y_1423_ = v___y_1441_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1441_);
                    crate::leanh::lean_dec_ref(v_e_u2082_1438_);
                    crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___x_1448_;
                }
            }
            5 => {
                if v_done_1464_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_1462_);
                    v_e_u2082_1438_ = v_e_x27_1463_;
                    v___y_1439_ = v___y_1454_;
                    v___y_1440_ = v___y_1459_;
                    v___y_1441_ = v___y_1460_;
                    v___y_1442_ = v___y_1458_;
                    v___y_1443_ = v___y_1455_;
                    v___y_1444_ = v___y_1461_;
                    v___y_1445_ = v___y_1457_;
                    v___y_1446_ = v___y_1456_;
                    v___y_1447_ = v___y_1453_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_x27_1463_);
                    crate::leanh::lean_dec_ref(v___y_1461_);
                    crate::leanh::lean_dec(v___y_1459_);
                    crate::leanh::lean_dec_ref(v___y_1458_);
                    crate::leanh::lean_dec(v___y_1457_);
                    crate::leanh::lean_dec_ref(v___y_1456_);
                    crate::leanh::lean_dec(v___y_1455_);
                    crate::leanh::lean_dec(v___y_1454_);
                    crate::leanh::lean_dec(v___y_1453_);
                    v_r_1422_ = v_a_1462_;
                    v___y_1423_ = v___y_1460_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_1475_) == 0 {
                    v_a_1476_ = crate::leanh::lean_ctor_get(v___y_1475_, 0);
                    crate::leanh::lean_inc(v_a_1476_);
                    crate::leanh::lean_dec_ref_known(v___y_1475_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1476_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_1474_);
                        crate::leanh::lean_dec(v___y_1472_);
                        crate::leanh::lean_dec(v___y_1471_);
                        crate::leanh::lean_dec_ref(v___y_1470_);
                        crate::leanh::lean_dec_ref(v___y_1469_);
                        crate::leanh::lean_dec(v___y_1468_);
                        crate::leanh::lean_dec(v___y_1467_);
                        crate::leanh::lean_dec(v___y_1466_);
                        v_r_1422_ = v_a_1476_;
                        v___y_1423_ = v___y_1473_;
                        state = 1;
                        continue;
                    } else {
                        v_e_x27_1477_ = crate::leanh::lean_ctor_get(v_a_1476_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_1477_);
                        v_done_1478_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_1476_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        v___y_1453_ = v___y_1467_;
                        v___y_1454_ = v___y_1466_;
                        v___y_1455_ = v___y_1468_;
                        v___y_1456_ = v___y_1469_;
                        v___y_1457_ = v___y_1471_;
                        v___y_1458_ = v___y_1470_;
                        v___y_1459_ = v___y_1472_;
                        v___y_1460_ = v___y_1473_;
                        v___y_1461_ = v___y_1474_;
                        v_a_1462_ = v_a_1476_;
                        v_e_x27_1463_ = v_e_x27_1477_;
                        v_done_1464_ = v_done_1478_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1474_);
                    crate::leanh::lean_dec(v___y_1473_);
                    crate::leanh::lean_dec(v___y_1472_);
                    crate::leanh::lean_dec(v___y_1471_);
                    crate::leanh::lean_dec_ref(v___y_1470_);
                    crate::leanh::lean_dec_ref(v___y_1469_);
                    crate::leanh::lean_dec(v___y_1468_);
                    crate::leanh::lean_dec(v___y_1467_);
                    crate::leanh::lean_dec(v___y_1466_);
                    crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___y_1475_;
                }
            }
            7 => {
                v___x_1602_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1603_ = lean_nat_dec_eq(v_maxRecDepth_1483_, v___x_1602_);
                if v___x_1603_ == 0 {
                    v___x_1604_ = lean_nat_dec_eq(v_currRecDepth_1482_, v_maxRecDepth_1483_);
                    if v___x_1604_ == 0 {
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1496_);
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1494_);
                        crate::leanh::lean_dec(v_cancelTk_x3f_1492_);
                        crate::leanh::lean_dec(v_currMacroScope_1490_);
                        crate::leanh::lean_dec(v_quotContext_1489_);
                        crate::leanh::lean_dec(v_maxHeartbeats_1488_);
                        crate::leanh::lean_dec(v_initHeartbeats_1487_);
                        crate::leanh::lean_dec(v_openDecls_1486_);
                        crate::leanh::lean_dec(v_currNamespace_1485_);
                        crate::leanh::lean_dec(v_maxRecDepth_1483_);
                        crate::leanh::lean_dec(v_currRecDepth_1482_);
                        crate::leanh::lean_dec_ref(v_options_1481_);
                        crate::leanh::lean_dec_ref(v_fileMap_1480_);
                        crate::leanh::lean_dec_ref(v_fileName_1479_);
                        crate::leanh::lean_dec(v_a_1419_);
                        crate::leanh::lean_dec(v_a_1417_);
                        crate::leanh::lean_dec_ref(v_a_1416_);
                        crate::leanh::lean_dec(v_a_1415_);
                        crate::leanh::lean_dec_ref(v_a_1414_);
                        crate::leanh::lean_dec(v_a_1413_);
                        crate::leanh::lean_dec(v_a_1412_);
                        crate::leanh::lean_dec(v_a_1411_);
                        crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                        v___x_1605_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_1484_);
                        return v___x_1605_;
                    }
                } else {
                    state = 18;
                    continue;
                }
            }
            8 => {
                v___x_1509_ = lean_st_ref_take(v___y_1502_);
                v_cache_1510_ = crate::leanh::lean_ctor_get(v___x_1509_, 1);
                v_isSharedCheck_1543_ = (!crate::leanh::lean_is_exclusive(v___x_1509_)) as u8;
                if v_isSharedCheck_1543_ == 0 {
                    v_unused_1544_ = crate::leanh::lean_ctor_get(v___x_1509_, 0);
                    crate::leanh::lean_dec(v_unused_1544_);
                    v___x_1512_ = v___x_1509_;
                    v_isShared_1513_ = v_isSharedCheck_1543_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_1510_);
                    crate::leanh::lean_dec(v___x_1509_);
                    v___x_1512_ = crate::leanh::lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1543_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1512_, 0, v___y_1499_);
                    v___x_1515_ = v___x_1512_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___y_1499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_cache_1510_);
                    v___x_1515_ = v_reuseFailAlloc_1542_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1516_ = lean_st_ref_set(v___y_1502_, v___x_1515_);
                v_pre_1517_ = crate::leanh::lean_ctor_get(v___y_1500_, 0);
                crate::leanh::lean_inc_ref(v_pre_1517_);
                crate::leanh::lean_inc(v___y_1508_);
                crate::leanh::lean_inc_ref(v___y_1507_);
                crate::leanh::lean_inc(v___y_1506_);
                crate::leanh::lean_inc_ref(v___y_1505_);
                crate::leanh::lean_inc(v___y_1504_);
                crate::leanh::lean_inc_ref(v___y_1503_);
                crate::leanh::lean_inc(v___y_1502_);
                crate::leanh::lean_inc(v___y_1501_);
                crate::leanh::lean_inc(v___y_1500_);
                crate::leanh::lean_inc_ref(v_e_u2081_1410_);
                v___x_1518_ = crate::leanh::lean_apply_11(
                    v_pre_1517_,
                    v_e_u2081_1410_,
                    v___y_1500_,
                    v___y_1501_,
                    v___y_1502_,
                    v___y_1503_,
                    v___y_1504_,
                    v___y_1505_,
                    v___y_1506_,
                    v___y_1507_,
                    v___y_1508_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1518_) == 0 {
                    v_a_1519_ = crate::leanh::lean_ctor_get(v___x_1518_, 0);
                    crate::leanh::lean_inc(v_a_1519_);
                    crate::leanh::lean_dec_ref_known(v___x_1518_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1519_) == 0 {
                        v_done_1520_ = crate::leanh::lean_ctor_get_uint8(v_a_1519_, 0 as u32);
                        if v_done_1520_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_1519_, 0);
                            crate::leanh::lean_inc_ref(v_e_u2081_1410_);
                            v___x_1521_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_u2081_1410_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
                            if crate::leanh::lean_obj_tag(v___x_1521_) == 0 {
                                v_a_1522_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                                crate::leanh::lean_inc(v_a_1522_);
                                v___x_1523_ = crate::leanh::lean_box(0);
                                if crate::leanh::lean_obj_tag(v_a_1522_) == 0 {
                                    v_done_1524_ =
                                        crate::leanh::lean_ctor_get_uint8(v_a_1522_, 0 as u32);
                                    crate::leanh::lean_dec_ref_known(v_a_1522_, 0);
                                    if v_done_1524_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1521_, 1);
                                        crate::leanh::lean_inc_ref(v_e_u2081_1410_);
                                        v___x_1525_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_1523_, v_e_u2081_1410_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
                                        v___y_1466_ = v___y_1500_;
                                        v___y_1467_ = v___y_1508_;
                                        v___y_1468_ = v___y_1504_;
                                        v___y_1469_ = v___y_1507_;
                                        v___y_1470_ = v___y_1503_;
                                        v___y_1471_ = v___y_1506_;
                                        v___y_1472_ = v___y_1501_;
                                        v___y_1473_ = v___y_1502_;
                                        v___y_1474_ = v___y_1505_;
                                        v___y_1475_ = v___x_1525_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___y_1466_ = v___y_1500_;
                                        v___y_1467_ = v___y_1508_;
                                        v___y_1468_ = v___y_1504_;
                                        v___y_1469_ = v___y_1507_;
                                        v___y_1470_ = v___y_1503_;
                                        v___y_1471_ = v___y_1506_;
                                        v___y_1472_ = v___y_1501_;
                                        v___y_1473_ = v___y_1502_;
                                        v___y_1474_ = v___y_1505_;
                                        v___y_1475_ = v___x_1521_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    v_done_1526_ = crate::leanh::lean_ctor_get_uint8(
                                        v_a_1522_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                    );
                                    if v_done_1526_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1521_, 1);
                                        v_e_x27_1527_ = crate::leanh::lean_ctor_get(v_a_1522_, 0);
                                        v_isSharedCheck_1539_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_1522_)) as u8;
                                        if v_isSharedCheck_1539_ == 0 {
                                            v___x_1529_ = v_a_1522_;
                                            v_isShared_1530_ = v_isSharedCheck_1539_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_e_x27_1527_);
                                            crate::leanh::lean_dec(v_a_1522_);
                                            v___x_1529_ = crate::leanh::lean_box(0);
                                            v_isShared_1530_ = v_isSharedCheck_1539_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_a_1522_, 1);
                                        v___y_1466_ = v___y_1500_;
                                        v___y_1467_ = v___y_1508_;
                                        v___y_1468_ = v___y_1504_;
                                        v___y_1469_ = v___y_1507_;
                                        v___y_1470_ = v___y_1503_;
                                        v___y_1471_ = v___y_1506_;
                                        v___y_1472_ = v___y_1501_;
                                        v___y_1473_ = v___y_1502_;
                                        v___y_1474_ = v___y_1505_;
                                        v___y_1475_ = v___x_1521_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                v___y_1466_ = v___y_1500_;
                                v___y_1467_ = v___y_1508_;
                                v___y_1468_ = v___y_1504_;
                                v___y_1469_ = v___y_1507_;
                                v___y_1470_ = v___y_1503_;
                                v___y_1471_ = v___y_1506_;
                                v___y_1472_ = v___y_1501_;
                                v___y_1473_ = v___y_1502_;
                                v___y_1474_ = v___y_1505_;
                                v___y_1475_ = v___x_1521_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_1508_);
                            crate::leanh::lean_dec_ref(v___y_1507_);
                            crate::leanh::lean_dec(v___y_1506_);
                            crate::leanh::lean_dec_ref(v___y_1505_);
                            crate::leanh::lean_dec(v___y_1504_);
                            crate::leanh::lean_dec_ref(v___y_1503_);
                            crate::leanh::lean_dec(v___y_1501_);
                            crate::leanh::lean_dec(v___y_1500_);
                            v_r_1422_ = v_a_1519_;
                            v___y_1423_ = v___y_1502_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_done_1540_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_1519_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_done_1540_ == 0 {
                            v_e_x27_1541_ = crate::leanh::lean_ctor_get(v_a_1519_, 0);
                            crate::leanh::lean_inc_ref(v_e_x27_1541_);
                            crate::leanh::lean_dec_ref_known(v_a_1519_, 1);
                            v_e_u2082_1438_ = v_e_x27_1541_;
                            v___y_1439_ = v___y_1500_;
                            v___y_1440_ = v___y_1501_;
                            v___y_1441_ = v___y_1502_;
                            v___y_1442_ = v___y_1503_;
                            v___y_1443_ = v___y_1504_;
                            v___y_1444_ = v___y_1505_;
                            v___y_1445_ = v___y_1506_;
                            v___y_1446_ = v___y_1507_;
                            v___y_1447_ = v___y_1508_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_1508_);
                            crate::leanh::lean_dec_ref(v___y_1507_);
                            crate::leanh::lean_dec(v___y_1506_);
                            crate::leanh::lean_dec_ref(v___y_1505_);
                            crate::leanh::lean_dec(v___y_1504_);
                            crate::leanh::lean_dec_ref(v___y_1503_);
                            crate::leanh::lean_dec(v___y_1501_);
                            crate::leanh::lean_dec(v___y_1500_);
                            v_r_1422_ = v_a_1519_;
                            v___y_1423_ = v___y_1502_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1508_);
                    crate::leanh::lean_dec_ref(v___y_1507_);
                    crate::leanh::lean_dec(v___y_1506_);
                    crate::leanh::lean_dec_ref(v___y_1505_);
                    crate::leanh::lean_dec(v___y_1504_);
                    crate::leanh::lean_dec_ref(v___y_1503_);
                    crate::leanh::lean_dec(v___y_1502_);
                    crate::leanh::lean_dec(v___y_1501_);
                    crate::leanh::lean_dec(v___y_1500_);
                    crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___x_1518_;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref(v_e_x27_1527_);
                v___x_1531_ =
                    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(
                        v___x_1523_,
                        v_e_x27_1527_,
                        v___y_1500_,
                        v___y_1501_,
                        v___y_1502_,
                        v___y_1503_,
                        v___y_1504_,
                        v___y_1505_,
                        v___y_1506_,
                        v___y_1507_,
                        v___y_1508_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    crate::leanh::lean_inc(v_a_1532_);
                    crate::leanh::lean_dec_ref_known(v___x_1531_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1532_) == 0 {
                        v_done_1533_ = crate::leanh::lean_ctor_get_uint8(v_a_1532_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_a_1532_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_1527_);
                        if v_isShared_1530_ == 0 {
                            v___x_1535_ = v___x_1529_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1536_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_e_x27_1527_);
                            v___x_1535_ = v_reuseFailAlloc_1536_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1529_);
                        crate::leanh::lean_dec_ref(v_e_x27_1527_);
                        v_e_x27_1537_ = crate::leanh::lean_ctor_get(v_a_1532_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_1537_);
                        v_done_1538_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_1532_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        v___y_1453_ = v___y_1508_;
                        v___y_1454_ = v___y_1500_;
                        v___y_1455_ = v___y_1504_;
                        v___y_1456_ = v___y_1507_;
                        v___y_1457_ = v___y_1506_;
                        v___y_1458_ = v___y_1503_;
                        v___y_1459_ = v___y_1501_;
                        v___y_1460_ = v___y_1502_;
                        v___y_1461_ = v___y_1505_;
                        v_a_1462_ = v_a_1532_;
                        v_e_x27_1463_ = v_e_x27_1537_;
                        v_done_1464_ = v_done_1538_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1529_);
                    crate::leanh::lean_dec_ref(v_e_x27_1527_);
                    crate::leanh::lean_dec(v___y_1508_);
                    crate::leanh::lean_dec_ref(v___y_1507_);
                    crate::leanh::lean_dec(v___y_1506_);
                    crate::leanh::lean_dec_ref(v___y_1505_);
                    crate::leanh::lean_dec(v___y_1504_);
                    crate::leanh::lean_dec_ref(v___y_1503_);
                    crate::leanh::lean_dec(v___y_1502_);
                    crate::leanh::lean_dec(v___y_1501_);
                    crate::leanh::lean_dec(v___y_1500_);
                    crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___x_1531_;
                }
            }
            12 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1535_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_done_1533_,
                );
                v___y_1453_ = v___y_1508_;
                v___y_1454_ = v___y_1500_;
                v___y_1455_ = v___y_1504_;
                v___y_1456_ = v___y_1507_;
                v___y_1457_ = v___y_1506_;
                v___y_1458_ = v___y_1503_;
                v___y_1459_ = v___y_1501_;
                v___y_1460_ = v___y_1502_;
                v___y_1461_ = v___y_1505_;
                v_a_1462_ = v___x_1535_;
                v_e_x27_1463_ = v_e_x27_1527_;
                v_done_1464_ = v_done_1533_;
                state = 5;
                continue;
            }
            13 => {
                v___x_1557_ = lean_st_ref_get(v___y_1550_);
                v_cache_1558_ = crate::leanh::lean_ctor_get(v___x_1557_, 1);
                crate::leanh::lean_inc_ref(v_cache_1558_);
                crate::leanh::lean_dec(v___x_1557_);
                v___x_1559_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_cache_1558_, v_e_u2081_1410_);
                crate::leanh::lean_dec_ref(v_cache_1558_);
                if crate::leanh::lean_obj_tag(v___x_1559_) == 1 {
                    crate::leanh::lean_dec(v___y_1556_);
                    crate::leanh::lean_dec_ref(v___y_1555_);
                    crate::leanh::lean_dec(v___y_1554_);
                    crate::leanh::lean_dec_ref(v___y_1553_);
                    crate::leanh::lean_dec(v___y_1552_);
                    crate::leanh::lean_dec_ref(v___y_1551_);
                    crate::leanh::lean_dec(v___y_1550_);
                    crate::leanh::lean_dec(v___y_1549_);
                    crate::leanh::lean_dec(v___y_1548_);
                    crate::leanh::lean_dec(v___y_1546_);
                    crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                    v_val_1560_ = crate::leanh::lean_ctor_get(v___x_1559_, 0);
                    v_isSharedCheck_1567_ = (!crate::leanh::lean_is_exclusive(v___x_1559_)) as u8;
                    if v_isSharedCheck_1567_ == 0 {
                        v___x_1562_ = v___x_1559_;
                        v_isShared_1563_ = v_isSharedCheck_1567_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1560_);
                        crate::leanh::lean_dec(v___x_1559_);
                        v___x_1562_ = crate::leanh::lean_box(0);
                        v_isShared_1563_ = v_isSharedCheck_1567_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1559_);
                    v___x_1568_ = lean_nat_add(v___y_1546_, v___y_1547_);
                    crate::leanh::lean_dec(v___y_1546_);
                    v___x_1569_ = crate::leanh::lean_unsigned_to_nat(1000);
                    v___x_1570_ = lean_nat_mod(v___x_1568_, v___x_1569_);
                    v___x_1571_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1572_ = lean_nat_dec_eq(v___x_1570_, v___x_1571_);
                    crate::leanh::lean_dec(v___x_1570_);
                    if v___x_1572_ == 0 {
                        v___y_1499_ = v___x_1568_;
                        v___y_1500_ = v___y_1548_;
                        v___y_1501_ = v___y_1549_;
                        v___y_1502_ = v___y_1550_;
                        v___y_1503_ = v___y_1551_;
                        v___y_1504_ = v___y_1552_;
                        v___y_1505_ = v___y_1553_;
                        v___y_1506_ = v___y_1554_;
                        v___y_1507_ = v___y_1555_;
                        v___y_1508_ = v___y_1556_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1573_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0;
                        v___x_1574_ =
                            l_Lean_Core_checkSystem(v___x_1573_, v___y_1555_, v___y_1556_);
                        if crate::leanh::lean_obj_tag(v___x_1574_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1574_, 1);
                            v___y_1499_ = v___x_1568_;
                            v___y_1500_ = v___y_1548_;
                            v___y_1501_ = v___y_1549_;
                            v___y_1502_ = v___y_1550_;
                            v___y_1503_ = v___y_1551_;
                            v___y_1504_ = v___y_1552_;
                            v___y_1505_ = v___y_1553_;
                            v___y_1506_ = v___y_1554_;
                            v___y_1507_ = v___y_1555_;
                            v___y_1508_ = v___y_1556_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1568_);
                            crate::leanh::lean_dec(v___y_1556_);
                            crate::leanh::lean_dec_ref(v___y_1555_);
                            crate::leanh::lean_dec(v___y_1554_);
                            crate::leanh::lean_dec_ref(v___y_1553_);
                            crate::leanh::lean_dec(v___y_1552_);
                            crate::leanh::lean_dec_ref(v___y_1551_);
                            crate::leanh::lean_dec(v___y_1550_);
                            crate::leanh::lean_dec(v___y_1549_);
                            crate::leanh::lean_dec(v___y_1548_);
                            crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                            v_a_1575_ = crate::leanh::lean_ctor_get(v___x_1574_, 0);
                            v_isSharedCheck_1582_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1574_)) as u8;
                            if v_isSharedCheck_1582_ == 0 {
                                v___x_1577_ = v___x_1574_;
                                v_isShared_1578_ = v_isSharedCheck_1582_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1575_);
                                crate::leanh::lean_dec(v___x_1574_);
                                v___x_1577_ = crate::leanh::lean_box(0);
                                v_isShared_1578_ = v_isSharedCheck_1582_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                if v_isShared_1563_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1562_, 0);
                    v___x_1565_ = v___x_1562_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1560_);
                    v___x_1565_ = v_reuseFailAlloc_1566_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1565_;
            }
            16 => {
                if v_isShared_1578_ == 0 {
                    v___x_1580_ = v___x_1577_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1580_;
            }
            18 => {
                v___x_1584_ = lean_st_ref_get(v_a_1413_);
                v_numSteps_1585_ = crate::leanh::lean_ctor_get(v___x_1584_, 0);
                crate::leanh::lean_inc(v_numSteps_1585_);
                crate::leanh::lean_dec(v___x_1584_);
                v___x_1586_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1587_ = lean_nat_add(v_currRecDepth_1482_, v___x_1586_);
                crate::leanh::lean_dec(v_currRecDepth_1482_);
                if v_isShared_1497_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1496_, 3, v___x_1587_);
                    v___x_1589_ = v___x_1496_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_fileName_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_fileMap_1480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_options_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___x_1587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_maxRecDepth_1483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 5, v_ref_1484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 6, v_currNamespace_1485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 7, v_openDecls_1486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 8, v_initHeartbeats_1487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 9, v_maxHeartbeats_1488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 10, v_quotContext_1489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 11, v_currMacroScope_1490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 12, v_cancelTk_x3f_1492_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1601_,
                        13,
                        v_inheritedTraceOptions_1494_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1601_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_1491_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1601_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1493_,
                    );
                    v___x_1589_ = v_reuseFailAlloc_1601_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1590_ = lean_nat_dec_le(v_a_1412_, v_numSteps_1585_);
                if v___x_1590_ == 0 {
                    v___y_1546_ = v_numSteps_1585_;
                    v___y_1547_ = v___x_1586_;
                    v___y_1548_ = v_a_1411_;
                    v___y_1549_ = v_a_1412_;
                    v___y_1550_ = v_a_1413_;
                    v___y_1551_ = v_a_1414_;
                    v___y_1552_ = v_a_1415_;
                    v___y_1553_ = v_a_1416_;
                    v___y_1554_ = v_a_1417_;
                    v___y_1555_ = v___x_1589_;
                    v___y_1556_ = v_a_1419_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_numSteps_1585_);
                    crate::leanh::lean_dec(v_a_1415_);
                    crate::leanh::lean_dec_ref(v_a_1414_);
                    crate::leanh::lean_dec(v_a_1413_);
                    crate::leanh::lean_dec(v_a_1412_);
                    crate::leanh::lean_dec(v_a_1411_);
                    crate::leanh::lean_dec_ref(v_e_u2081_1410_);
                    v___x_1591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once), _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2);
                    v___x_1592_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_1591_, v_a_1416_, v_a_1417_, v___x_1589_, v_a_1419_);
                    crate::leanh::lean_dec(v_a_1419_);
                    crate::leanh::lean_dec_ref(v___x_1589_);
                    crate::leanh::lean_dec(v_a_1417_);
                    crate::leanh::lean_dec_ref(v_a_1416_);
                    v_a_1593_ = crate::leanh::lean_ctor_get(v___x_1592_, 0);
                    v_isSharedCheck_1600_ = (!crate::leanh::lean_is_exclusive(v___x_1592_)) as u8;
                    if v_isSharedCheck_1600_ == 0 {
                        v___x_1595_ = v___x_1592_;
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1593_);
                        crate::leanh::lean_dec(v___x_1592_);
                        v___x_1595_ = crate::leanh::lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_1596_ == 0 {
                    v___x_1598_ = v___x_1595_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
                    v___x_1598_ = v_reuseFailAlloc_1599_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(
    mut v_e_u2081_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
    mut v_a_1610_: *mut crate::leanh::LeanObject,
    mut v_a_1611_: *mut crate::leanh::LeanObject,
    mut v_a_1612_: *mut crate::leanh::LeanObject,
    mut v_a_1613_: *mut crate::leanh::LeanObject,
    mut v_a_1614_: *mut crate::leanh::LeanObject,
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1618_ = lean_sym_dsimp(
        v_e_u2081_1607_,
        v_a_1608_,
        v_a_1609_,
        v_a_1610_,
        v_a_1611_,
        v_a_1612_,
        v_a_1613_,
        v_a_1614_,
        v_a_1615_,
        v_a_1616_,
    );
    return v_res_1618_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(
    mut v_00_u03b2_1619_: *mut crate::leanh::LeanObject,
    mut v_x_1620_: *mut crate::leanh::LeanObject,
    mut v_x_1621_: *mut crate::leanh::LeanObject,
    mut v_x_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_x_1620_, v_x_1621_, v_x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(
    mut v_00_u03b2_1624_: *mut crate::leanh::LeanObject,
    mut v_x_1625_: *mut crate::leanh::LeanObject,
    mut v_x_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_1625_, v_x_1626_);
    return v___x_1627_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(
    mut v_00_u03b2_1628_: *mut crate::leanh::LeanObject,
    mut v_x_1629_: *mut crate::leanh::LeanObject,
    mut v_x_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(v_00_u03b2_1628_, v_x_1629_, v_x_1630_);
    crate::leanh::lean_dec_ref(v_x_1630_);
    crate::leanh::lean_dec_ref(v_x_1629_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(
    mut v_00_u03b2_1632_: *mut crate::leanh::LeanObject,
    mut v_x_1633_: *mut crate::leanh::LeanObject,
    mut v_x_1634_: usize,
    mut v_x_1635_: usize,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
    mut v_x_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_1633_, v_x_1634_, v_x_1635_, v_x_1636_, v_x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(
    mut v_00_u03b2_1639_: *mut crate::leanh::LeanObject,
    mut v_x_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: *mut crate::leanh::LeanObject,
    mut v_x_1643_: *mut crate::leanh::LeanObject,
    mut v_x_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_43095__boxed_1645_: usize = 0;
    let mut v_x_43096__boxed_1646_: usize = 0;
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_43095__boxed_1645_ = crate::leanh::lean_unbox_usize(v_x_1641_);
    crate::leanh::lean_dec(v_x_1641_);
    v_x_43096__boxed_1646_ = crate::leanh::lean_unbox_usize(v_x_1642_);
    crate::leanh::lean_dec(v_x_1642_);
    v_res_1647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(v_00_u03b2_1639_, v_x_1640_, v_x_43095__boxed_1645_, v_x_43096__boxed_1646_, v_x_1643_, v_x_1644_);
    return v_res_1647_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(
    mut v_00_u03b2_1648_: *mut crate::leanh::LeanObject,
    mut v_x_1649_: *mut crate::leanh::LeanObject,
    mut v_x_1650_: usize,
    mut v_x_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_1649_, v_x_1650_, v_x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(
    mut v_00_u03b2_1653_: *mut crate::leanh::LeanObject,
    mut v_x_1654_: *mut crate::leanh::LeanObject,
    mut v_x_1655_: *mut crate::leanh::LeanObject,
    mut v_x_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_43112__boxed_1657_: usize = 0;
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_43112__boxed_1657_ = crate::leanh::lean_unbox_usize(v_x_1655_);
    crate::leanh::lean_dec(v_x_1655_);
    v_res_1658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(v_00_u03b2_1653_, v_x_1654_, v_x_43112__boxed_1657_, v_x_1656_);
    crate::leanh::lean_dec_ref(v_x_1656_);
    crate::leanh::lean_dec_ref(v_x_1654_);
    return v_res_1658_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1659_: *mut crate::leanh::LeanObject,
    mut v_n_1660_: *mut crate::leanh::LeanObject,
    mut v_k_1661_: *mut crate::leanh::LeanObject,
    mut v_v_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v_n_1660_, v_k_1661_, v_v_1662_);
    return v___x_1663_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1664_: *mut crate::leanh::LeanObject,
    mut v_depth_1665_: usize,
    mut v_keys_1666_: *mut crate::leanh::LeanObject,
    mut v_vals_1667_: *mut crate::leanh::LeanObject,
    mut v_heq_1668_: *mut crate::leanh::LeanObject,
    mut v_i_1669_: *mut crate::leanh::LeanObject,
    mut v_entries_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1665_, v_keys_1666_, v_vals_1667_, v_i_1669_, v_entries_1670_);
    return v___x_1671_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_1672_: *mut crate::leanh::LeanObject,
    mut v_depth_1673_: *mut crate::leanh::LeanObject,
    mut v_keys_1674_: *mut crate::leanh::LeanObject,
    mut v_vals_1675_: *mut crate::leanh::LeanObject,
    mut v_heq_1676_: *mut crate::leanh::LeanObject,
    mut v_i_1677_: *mut crate::leanh::LeanObject,
    mut v_entries_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1679_: usize = 0;
    let mut v_res_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1679_ = crate::leanh::lean_unbox_usize(v_depth_1673_);
    crate::leanh::lean_dec(v_depth_1673_);
    v_res_1680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1672_, v_depth_boxed_1679_, v_keys_1674_, v_vals_1675_, v_heq_1676_, v_i_1677_, v_entries_1678_);
    crate::leanh::lean_dec_ref(v_vals_1675_);
    crate::leanh::lean_dec_ref(v_keys_1674_);
    return v_res_1680_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(
    mut v_00_u03b2_1681_: *mut crate::leanh::LeanObject,
    mut v_keys_1682_: *mut crate::leanh::LeanObject,
    mut v_vals_1683_: *mut crate::leanh::LeanObject,
    mut v_heq_1684_: *mut crate::leanh::LeanObject,
    mut v_i_1685_: *mut crate::leanh::LeanObject,
    mut v_k_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1682_, v_vals_1683_, v_i_1685_, v_k_1686_);
    return v___x_1687_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_1688_: *mut crate::leanh::LeanObject,
    mut v_keys_1689_: *mut crate::leanh::LeanObject,
    mut v_vals_1690_: *mut crate::leanh::LeanObject,
    mut v_heq_1691_: *mut crate::leanh::LeanObject,
    mut v_i_1692_: *mut crate::leanh::LeanObject,
    mut v_k_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1688_, v_keys_1689_, v_vals_1690_, v_heq_1691_, v_i_1692_, v_k_1693_);
    crate::leanh::lean_dec_ref(v_k_1693_);
    crate::leanh::lean_dec_ref(v_vals_1690_);
    crate::leanh::lean_dec_ref(v_keys_1689_);
    return v_res_1694_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1695_: *mut crate::leanh::LeanObject,
    mut v_x_1696_: *mut crate::leanh::LeanObject,
    mut v_x_1697_: *mut crate::leanh::LeanObject,
    mut v_x_1698_: *mut crate::leanh::LeanObject,
    mut v_x_1699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1696_, v_x_1697_, v_x_1698_, v_x_1699_);
    return v___x_1700_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Main(
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
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Main(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Main(builtin);
}
