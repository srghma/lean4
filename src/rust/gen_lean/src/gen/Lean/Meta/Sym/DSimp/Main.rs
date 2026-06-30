// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Main
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.DSimp.DSimproc Lean.Meta.Sym.DSimp.App Lean.Meta.Sym.DSimp.Lambda Lean.Meta.Sym.DSimp.Forall Lean.Meta.Sym.DSimp.Let Lean.Meta.Sym.AlphaShareBuilder
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mod, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
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
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value: leanh::LeanStringObject<56> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 101, 114, 110, 101, 108, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 101, 114, 109, 32, 100, 117, 114, 105, 110, 103, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [10, 112, 114, 101, 45, 112, 114, 111, 99, 101, 115, 115, 32, 97, 110, 100, 32, 102, 111, 108, 100, 32, 116, 104, 101, 109, 32, 97, 115, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value: leanh::LeanStringObject<49> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [96, 100, 115, 105, 109, 112, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 115, 116, 101, 112, 115, 32, 101, 120, 99, 101, 101, 100, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(
    mut v_d_851_: *mut leanh::LeanObject,
    mut v_e_852_: *mut leanh::LeanObject,
    mut v___y_853_: *mut leanh::LeanObject,
    mut v___y_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
    mut v___y_856_: *mut leanh::LeanObject,
    mut v___y_857_: *mut leanh::LeanObject,
    mut v___y_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_865_: u8 = 0;
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_864_ = lean_st_ref_get(v___y_854_);
                v_debug_865_ = leanh::lean_ctor_get_uint8(
                    v___x_864_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_864_);
                if v_debug_865_ == 0 {
                    v___y_861_ = v___y_854_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_e_852_);
                    v___x_866_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_e_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_,
                        v___y_858_,
                    );
                    if leanh::lean_obj_tag(v___x_866_) == 0 {
                        leanh::lean_dec_ref_known(v___x_866_, 1);
                        v___y_861_ = v___y_854_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_852_);
                        leanh::lean_dec(v_d_851_);
                        v_a_867_ = leanh::lean_ctor_get(v___x_866_, 0);
                        v_isSharedCheck_874_ = (!leanh::lean_is_exclusive(v___x_866_)) as u8;
                        if v_isSharedCheck_874_ == 0 {
                            v___x_869_ = v___x_866_;
                            v_isShared_870_ = v_isSharedCheck_874_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_867_);
                            leanh::lean_dec(v___x_866_);
                            v___x_869_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
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
    mut v_d_875_: *mut leanh::LeanObject,
    mut v_e_876_: *mut leanh::LeanObject,
    mut v___y_877_: *mut leanh::LeanObject,
    mut v___y_878_: *mut leanh::LeanObject,
    mut v___y_879_: *mut leanh::LeanObject,
    mut v___y_880_: *mut leanh::LeanObject,
    mut v___y_881_: *mut leanh::LeanObject,
    mut v___y_882_: *mut leanh::LeanObject,
    mut v___y_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_875_, v_e_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
    leanh::lean_dec(v___y_882_);
    leanh::lean_dec_ref(v___y_881_);
    leanh::lean_dec(v___y_880_);
    leanh::lean_dec_ref(v___y_879_);
    leanh::lean_dec(v___y_878_);
    leanh::lean_dec_ref(v___y_877_);
    return v_res_884_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(
    mut v_d_885_: *mut leanh::LeanObject,
    mut v_e_886_: *mut leanh::LeanObject,
    mut v___y_887_: *mut leanh::LeanObject,
    mut v___y_888_: *mut leanh::LeanObject,
    mut v___y_889_: *mut leanh::LeanObject,
    mut v___y_890_: *mut leanh::LeanObject,
    mut v___y_891_: *mut leanh::LeanObject,
    mut v___y_892_: *mut leanh::LeanObject,
    mut v___y_893_: *mut leanh::LeanObject,
    mut v___y_894_: *mut leanh::LeanObject,
    mut v___y_895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_885_, v_e_886_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
    return v___x_897_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(
    mut v_d_898_: *mut leanh::LeanObject,
    mut v_e_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
    mut v___y_901_: *mut leanh::LeanObject,
    mut v___y_902_: *mut leanh::LeanObject,
    mut v___y_903_: *mut leanh::LeanObject,
    mut v___y_904_: *mut leanh::LeanObject,
    mut v___y_905_: *mut leanh::LeanObject,
    mut v___y_906_: *mut leanh::LeanObject,
    mut v___y_907_: *mut leanh::LeanObject,
    mut v___y_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(v_d_898_, v_e_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
    leanh::lean_dec(v___y_908_);
    leanh::lean_dec_ref(v___y_907_);
    leanh::lean_dec(v___y_906_);
    leanh::lean_dec_ref(v___y_905_);
    leanh::lean_dec(v___y_904_);
    leanh::lean_dec_ref(v___y_903_);
    leanh::lean_dec(v___y_902_);
    leanh::lean_dec(v___y_901_);
    leanh::lean_dec(v___y_900_);
    return v_res_910_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(
    mut v_msgData_911_: *mut leanh::LeanObject,
    mut v___y_912_: *mut leanh::LeanObject,
    mut v___y_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = lean_st_ref_get(v___y_915_);
    v_env_918_ = leanh::lean_ctor_get(v___x_917_, 0);
    leanh::lean_inc_ref(v_env_918_);
    leanh::lean_dec(v___x_917_);
    v___x_919_ = lean_st_ref_get(v___y_913_);
    v_mctx_920_ = leanh::lean_ctor_get(v___x_919_, 0);
    leanh::lean_inc_ref(v_mctx_920_);
    leanh::lean_dec(v___x_919_);
    v_lctx_921_ = leanh::lean_ctor_get(v___y_912_, 2);
    v_options_922_ = leanh::lean_ctor_get(v___y_914_, 2);
    leanh::lean_inc_ref(v_options_922_);
    leanh::lean_inc_ref(v_lctx_921_);
    v___x_923_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v_env_918_);
    leanh::lean_ctor_set(v___x_923_, 1, v_mctx_920_);
    leanh::lean_ctor_set(v___x_923_, 2, v_lctx_921_);
    leanh::lean_ctor_set(v___x_923_, 3, v_options_922_);
    v___x_924_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_924_, 0, v___x_923_);
    leanh::lean_ctor_set(v___x_924_, 1, v_msgData_911_);
    v___x_925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_925_, 0, v___x_924_);
    return v___x_925_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(
    mut v_msgData_926_: *mut leanh::LeanObject,
    mut v___y_927_: *mut leanh::LeanObject,
    mut v___y_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_932_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
    leanh::lean_dec(v___y_930_);
    leanh::lean_dec_ref(v___y_929_);
    leanh::lean_dec(v___y_928_);
    leanh::lean_dec_ref(v___y_927_);
    return v_res_932_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(
    mut v_msg_933_: *mut leanh::LeanObject,
    mut v___y_934_: *mut leanh::LeanObject,
    mut v___y_935_: *mut leanh::LeanObject,
    mut v___y_936_: *mut leanh::LeanObject,
    mut v___y_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_939_ = leanh::lean_ctor_get(v___y_936_, 5);
                v___x_940_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
                v_a_941_ = leanh::lean_ctor_get(v___x_940_, 0);
                v_isSharedCheck_949_ = (!leanh::lean_is_exclusive(v___x_940_)) as u8;
                if v_isSharedCheck_949_ == 0 {
                    v___x_943_ = v___x_940_;
                    v_isShared_944_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_941_);
                    leanh::lean_dec(v___x_940_);
                    v___x_943_ = leanh::lean_box(0);
                    v_isShared_944_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_939_);
                v___x_945_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_945_, 0, v_ref_939_);
                leanh::lean_ctor_set(v___x_945_, 1, v_a_941_);
                if v_isShared_944_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_943_, 1);
                    leanh::lean_ctor_set(v___x_943_, 0, v___x_945_);
                    v___x_947_ = v___x_943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
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
    mut v_msg_950_: *mut leanh::LeanObject,
    mut v___y_951_: *mut leanh::LeanObject,
    mut v___y_952_: *mut leanh::LeanObject,
    mut v___y_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
    leanh::lean_dec(v___y_954_);
    leanh::lean_dec_ref(v___y_953_);
    leanh::lean_dec(v___y_952_);
    leanh::lean_dec_ref(v___y_951_);
    return v_res_956_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1;
    v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
    return v___x_961_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3;
    v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
    return v___x_964_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(
    mut v_e_965_: *mut leanh::LeanObject,
    mut v_a_966_: *mut leanh::LeanObject,
    mut v_a_967_: *mut leanh::LeanObject,
    mut v_a_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
    mut v_a_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
    mut v_a_972_: *mut leanh::LeanObject,
    mut v_a_973_: *mut leanh::LeanObject,
    mut v_a_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: u8 = 0;
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_965_) {
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
                    v_data_985_ = leanh::lean_ctor_get(v_e_965_, 0);
                    v_expr_986_ = leanh::lean_ctor_get(v_e_965_, 1);
                    leanh::lean_inc(v_a_974_);
                    leanh::lean_inc_ref(v_a_973_);
                    leanh::lean_inc(v_a_972_);
                    leanh::lean_inc_ref(v_a_971_);
                    leanh::lean_inc(v_a_970_);
                    leanh::lean_inc_ref(v_a_969_);
                    leanh::lean_inc(v_a_968_);
                    leanh::lean_inc(v_a_967_);
                    leanh::lean_inc(v_a_966_);
                    leanh::lean_inc_ref(v_expr_986_);
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
                    if leanh::lean_obj_tag(v___x_987_) == 0 {
                        v_a_988_ = leanh::lean_ctor_get(v___x_987_, 0);
                        v_isSharedCheck_1008_ =
                            (!leanh::lean_is_exclusive(v___x_987_)) as u8;
                        if v_isSharedCheck_1008_ == 0 {
                            v___x_990_ = v___x_987_;
                            v_isShared_991_ = v_isSharedCheck_1008_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_988_);
                            leanh::lean_dec(v___x_987_);
                            v___x_990_ = leanh::lean_box(0);
                            v_isShared_991_ = v_isSharedCheck_1008_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_965_, 2);
                        return v___x_987_;
                    }
                }
                11 => {
                    v___x_1009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once), _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2);
                    v___x_1010_ = l_Lean_indentExpr(v_e_965_);
                    v___x_1011_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1011_, 0, v___x_1009_);
                    leanh::lean_ctor_set(v___x_1011_, 1, v___x_1010_);
                    v___x_1012_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once), _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4);
                    v___x_1013_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1013_, 0, v___x_1011_);
                    leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
                    v___x_1014_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_1013_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
                    return v___x_1014_;
                }
                _ => {
                    leanh::lean_dec_ref(v_e_965_);
                    v___x_1015_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0;
                    v___x_1016_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
                    return v___x_1016_;
                }
            },
            1 => {
                v___x_978_ = 0;
                v___x_979_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_979_, 0, v_a_977_);
                leanh::lean_ctor_set_uint8(
                    v___x_979_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_978_,
                );
                v___x_980_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_980_, 0, v___x_979_);
                return v___x_980_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_988_) == 0 {
                    leanh::lean_dec_ref_known(v_a_988_, 0);
                    leanh::lean_dec_ref_known(v_e_965_, 2);
                    v___x_992_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0;
                    if v_isShared_991_ == 0 {
                        leanh::lean_ctor_set(v___x_990_, 0, v___x_992_);
                        v___x_994_ = v___x_990_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_995_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
                        v___x_994_ = v_reuseFailAlloc_995_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_990_);
                    v_e_x27_996_ = leanh::lean_ctor_get(v_a_988_, 0);
                    leanh::lean_inc_ref(v_e_x27_996_);
                    leanh::lean_dec_ref_known(v_a_988_, 1);
                    v___x_997_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_expr_986_,
                            v_e_x27_996_,
                        );
                    if v___x_997_ == 0 {
                        leanh::lean_inc(v_data_985_);
                        leanh::lean_dec_ref_known(v_e_965_, 2);
                        v___x_998_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_data_985_, v_e_x27_996_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
                        if leanh::lean_obj_tag(v___x_998_) == 0 {
                            v_a_999_ = leanh::lean_ctor_get(v___x_998_, 0);
                            leanh::lean_inc(v_a_999_);
                            leanh::lean_dec_ref_known(v___x_998_, 1);
                            v_a_977_ = v_a_999_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1000_ = leanh::lean_ctor_get(v___x_998_, 0);
                            v_isSharedCheck_1007_ =
                                (!leanh::lean_is_exclusive(v___x_998_)) as u8;
                            if v_isSharedCheck_1007_ == 0 {
                                v___x_1002_ = v___x_998_;
                                v_isShared_1003_ = v_isSharedCheck_1007_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1000_);
                                leanh::lean_dec(v___x_998_);
                                v___x_1002_ = leanh::lean_box(0);
                                v_isShared_1003_ = v_isSharedCheck_1007_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_x27_996_);
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
                    v_reuseFailAlloc_1006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
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
    mut v_e_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
    mut v_a_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
    mut v_a_1025_: *mut leanh::LeanObject,
    mut v_a_1026_: *mut leanh::LeanObject,
    mut v_a_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(
        v_e_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_,
        v_a_1025_, v_a_1026_,
    );
    leanh::lean_dec(v_a_1026_);
    leanh::lean_dec_ref(v_a_1025_);
    leanh::lean_dec(v_a_1024_);
    leanh::lean_dec_ref(v_a_1023_);
    leanh::lean_dec(v_a_1022_);
    leanh::lean_dec_ref(v_a_1021_);
    leanh::lean_dec(v_a_1020_);
    leanh::lean_dec(v_a_1019_);
    leanh::lean_dec(v_a_1018_);
    return v_res_1028_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(
    mut v_00_u03b1_1029_: *mut leanh::LeanObject,
    mut v_msg_1030_: *mut leanh::LeanObject,
    mut v___y_1031_: *mut leanh::LeanObject,
    mut v___y_1032_: *mut leanh::LeanObject,
    mut v___y_1033_: *mut leanh::LeanObject,
    mut v___y_1034_: *mut leanh::LeanObject,
    mut v___y_1035_: *mut leanh::LeanObject,
    mut v___y_1036_: *mut leanh::LeanObject,
    mut v___y_1037_: *mut leanh::LeanObject,
    mut v___y_1038_: *mut leanh::LeanObject,
    mut v___y_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1041_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_1030_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
    return v___x_1041_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(
    mut v_00_u03b1_1042_: *mut leanh::LeanObject,
    mut v_msg_1043_: *mut leanh::LeanObject,
    mut v___y_1044_: *mut leanh::LeanObject,
    mut v___y_1045_: *mut leanh::LeanObject,
    mut v___y_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
    mut v___y_1048_: *mut leanh::LeanObject,
    mut v___y_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
    mut v___y_1051_: *mut leanh::LeanObject,
    mut v___y_1052_: *mut leanh::LeanObject,
    mut v___y_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(v_00_u03b1_1042_, v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
    leanh::lean_dec(v___y_1052_);
    leanh::lean_dec_ref(v___y_1051_);
    leanh::lean_dec(v___y_1050_);
    leanh::lean_dec_ref(v___y_1049_);
    leanh::lean_dec(v___y_1048_);
    leanh::lean_dec_ref(v___y_1047_);
    leanh::lean_dec(v___y_1046_);
    leanh::lean_dec(v___y_1045_);
    leanh::lean_dec(v___y_1044_);
    return v_res_1054_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(
    mut v_e_1057_: *mut leanh::LeanObject,
    mut v_r_1058_: *mut leanh::LeanObject,
    mut v_a_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___f_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1061_ = lean_st_ref_take(v_a_1059_);
                v_numSteps_1062_ = leanh::lean_ctor_get(v___x_1061_, 0);
                v_cache_1063_ = leanh::lean_ctor_get(v___x_1061_, 1);
                v_isSharedCheck_1075_ = (!leanh::lean_is_exclusive(v___x_1061_)) as u8;
                if v_isSharedCheck_1075_ == 0 {
                    v___x_1065_ = v___x_1061_;
                    v_isShared_1066_ = v_isSharedCheck_1075_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_1063_);
                    leanh::lean_inc(v_numSteps_1062_);
                    leanh::lean_dec(v___x_1061_);
                    v___x_1065_ = leanh::lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1067_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0;
                v___f_1068_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1;
                leanh::lean_inc_ref(v_r_1058_);
                v___x_1069_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1067_,
                    v___f_1068_,
                    v_cache_1063_,
                    v_e_1057_,
                    v_r_1058_,
                );
                if v_isShared_1066_ == 0 {
                    leanh::lean_ctor_set(v___x_1065_, 1, v___x_1069_);
                    v___x_1071_ = v___x_1065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_numSteps_1062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1072_ = lean_st_ref_set(v_a_1059_, v___x_1071_);
                v___x_1073_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1073_, 0, v_r_1058_);
                return v___x_1073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(
    mut v_e_1076_: *mut leanh::LeanObject,
    mut v_r_1077_: *mut leanh::LeanObject,
    mut v_a_1078_: *mut leanh::LeanObject,
    mut v_a_1079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1080_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(
        v_e_1076_, v_r_1077_, v_a_1078_,
    );
    leanh::lean_dec(v_a_1078_);
    return v_res_1080_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(
    mut v_e_1081_: *mut leanh::LeanObject,
    mut v_r_1082_: *mut leanh::LeanObject,
    mut v_a_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_a_1086_: *mut leanh::LeanObject,
    mut v_a_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
    mut v_a_1089_: *mut leanh::LeanObject,
    mut v_a_1090_: *mut leanh::LeanObject,
    mut v_a_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___f_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = lean_st_ref_take(v_a_1085_);
                v_numSteps_1094_ = leanh::lean_ctor_get(v___x_1093_, 0);
                v_cache_1095_ = leanh::lean_ctor_get(v___x_1093_, 1);
                v_isSharedCheck_1107_ = (!leanh::lean_is_exclusive(v___x_1093_)) as u8;
                if v_isSharedCheck_1107_ == 0 {
                    v___x_1097_ = v___x_1093_;
                    v_isShared_1098_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_1095_);
                    leanh::lean_inc(v_numSteps_1094_);
                    leanh::lean_dec(v___x_1093_);
                    v___x_1097_ = leanh::lean_box(0);
                    v_isShared_1098_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1099_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0;
                v___f_1100_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1;
                leanh::lean_inc_ref(v_r_1082_);
                v___x_1101_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1099_,
                    v___f_1100_,
                    v_cache_1095_,
                    v_e_1081_,
                    v_r_1082_,
                );
                if v_isShared_1098_ == 0 {
                    leanh::lean_ctor_set(v___x_1097_, 1, v___x_1101_);
                    v___x_1103_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_numSteps_1094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1101_);
                    v___x_1103_ = v_reuseFailAlloc_1106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1104_ = lean_st_ref_set(v_a_1085_, v___x_1103_);
                v___x_1105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1105_, 0, v_r_1082_);
                return v___x_1105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(
    mut v_e_1108_: *mut leanh::LeanObject,
    mut v_r_1109_: *mut leanh::LeanObject,
    mut v_a_1110_: *mut leanh::LeanObject,
    mut v_a_1111_: *mut leanh::LeanObject,
    mut v_a_1112_: *mut leanh::LeanObject,
    mut v_a_1113_: *mut leanh::LeanObject,
    mut v_a_1114_: *mut leanh::LeanObject,
    mut v_a_1115_: *mut leanh::LeanObject,
    mut v_a_1116_: *mut leanh::LeanObject,
    mut v_a_1117_: *mut leanh::LeanObject,
    mut v_a_1118_: *mut leanh::LeanObject,
    mut v_a_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(
        v_e_1108_, v_r_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_,
        v_a_1116_, v_a_1117_, v_a_1118_,
    );
    leanh::lean_dec(v_a_1118_);
    leanh::lean_dec_ref(v_a_1117_);
    leanh::lean_dec(v_a_1116_);
    leanh::lean_dec_ref(v_a_1115_);
    leanh::lean_dec(v_a_1114_);
    leanh::lean_dec_ref(v_a_1113_);
    leanh::lean_dec(v_a_1112_);
    leanh::lean_dec(v_a_1111_);
    leanh::lean_dec(v_a_1110_);
    return v_res_1120_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1127_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3);
    v___x_1129_ = l_Lean_MessageData_ofFormat(v___x_1128_);
    return v___x_1129_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4);
    v___x_1131_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2;
    v___x_1132_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1132_, 0, v___x_1131_);
    leanh::lean_ctor_set(v___x_1132_, 1, v___x_1130_);
    return v___x_1132_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(
    mut v_ref_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5);
    v___x_1136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1136_, 0, v_ref_1133_);
    leanh::lean_ctor_set(v___x_1136_, 1, v___x_1135_);
    v___x_1137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(
    mut v_ref_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_1138_);
    return v_res_1140_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(
    mut v_00_u03b1_1141_: *mut leanh::LeanObject,
    mut v_ref_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
    mut v___y_1149_: *mut leanh::LeanObject,
    mut v___y_1150_: *mut leanh::LeanObject,
    mut v___y_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_1142_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(
    mut v_00_u03b1_1154_: *mut leanh::LeanObject,
    mut v_ref_1155_: *mut leanh::LeanObject,
    mut v___y_1156_: *mut leanh::LeanObject,
    mut v___y_1157_: *mut leanh::LeanObject,
    mut v___y_1158_: *mut leanh::LeanObject,
    mut v___y_1159_: *mut leanh::LeanObject,
    mut v___y_1160_: *mut leanh::LeanObject,
    mut v___y_1161_: *mut leanh::LeanObject,
    mut v___y_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
    mut v___y_1164_: *mut leanh::LeanObject,
    mut v___y_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(v_00_u03b1_1154_, v_ref_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
    leanh::lean_dec(v___y_1164_);
    leanh::lean_dec_ref(v___y_1163_);
    leanh::lean_dec(v___y_1162_);
    leanh::lean_dec_ref(v___y_1161_);
    leanh::lean_dec(v___y_1160_);
    leanh::lean_dec_ref(v___y_1159_);
    leanh::lean_dec(v___y_1158_);
    leanh::lean_dec(v___y_1157_);
    leanh::lean_dec(v___y_1156_);
    return v_res_1166_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(
    mut v_x_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
    mut v___y_1172_: *mut leanh::LeanObject,
    mut v___y_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_post_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_post_1179_ = leanh::lean_ctor_get(v___y_1169_, 1);
    leanh::lean_inc_ref(v_post_1179_);
    leanh::lean_inc(v___y_1177_);
    leanh::lean_inc_ref(v___y_1176_);
    leanh::lean_inc(v___y_1175_);
    leanh::lean_inc_ref(v___y_1174_);
    leanh::lean_inc(v___y_1173_);
    leanh::lean_inc_ref(v___y_1172_);
    leanh::lean_inc(v___y_1171_);
    leanh::lean_inc(v___y_1170_);
    leanh::lean_inc(v___y_1169_);
    v___x_1180_ = leanh::lean_apply_11(
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
        leanh::lean_box(0),
    );
    return v___x_1180_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(
    mut v_x_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
    mut v___y_1187_: *mut leanh::LeanObject,
    mut v___y_1188_: *mut leanh::LeanObject,
    mut v___y_1189_: *mut leanh::LeanObject,
    mut v___y_1190_: *mut leanh::LeanObject,
    mut v___y_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1191_);
    leanh::lean_dec_ref(v___y_1190_);
    leanh::lean_dec(v___y_1189_);
    leanh::lean_dec_ref(v___y_1188_);
    leanh::lean_dec(v___y_1187_);
    leanh::lean_dec_ref(v___y_1186_);
    leanh::lean_dec(v___y_1185_);
    leanh::lean_dec(v___y_1184_);
    leanh::lean_dec(v___y_1183_);
    return v_res_1193_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_1194_: *mut leanh::LeanObject,
    mut v_x_1195_: *mut leanh::LeanObject,
    mut v_x_1196_: *mut leanh::LeanObject,
    mut v_x_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: u8 = 0;
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1198_ = leanh::lean_ctor_get(v_x_1194_, 0);
                v_vs_1199_ = leanh::lean_ctor_get(v_x_1194_, 1);
                v_isSharedCheck_1223_ = (!leanh::lean_is_exclusive(v_x_1194_)) as u8;
                if v_isSharedCheck_1223_ == 0 {
                    v___x_1201_ = v_x_1194_;
                    v_isShared_1202_ = v_isSharedCheck_1223_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1199_);
                    leanh::lean_inc(v_ks_1198_);
                    leanh::lean_dec(v_x_1194_);
                    v___x_1201_ = leanh::lean_box(0);
                    v_isShared_1202_ = v_isSharedCheck_1223_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1203_ = lean_array_get_size(v_ks_1198_);
                v___x_1204_ = lean_nat_dec_lt(v_x_1195_, v___x_1203_);
                if v___x_1204_ == 0 {
                    leanh::lean_dec(v_x_1195_);
                    v___x_1205_ = lean_array_push(v_ks_1198_, v_x_1196_);
                    v___x_1206_ = lean_array_push(v_vs_1199_, v_x_1197_);
                    if v_isShared_1202_ == 0 {
                        leanh::lean_ctor_set(v___x_1201_, 1, v___x_1206_);
                        leanh::lean_ctor_set(v___x_1201_, 0, v___x_1205_);
                        v___x_1208_ = v___x_1201_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1209_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1205_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_ks_1198_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_vs_1199_);
                            v___x_1213_ = v_reuseFailAlloc_1217_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1218_ = lean_array_fset(v_ks_1198_, v_x_1195_, v_x_1196_);
                        v___x_1219_ = lean_array_fset(v_vs_1199_, v_x_1195_, v_x_1197_);
                        leanh::lean_dec(v_x_1195_);
                        if v_isShared_1202_ == 0 {
                            leanh::lean_ctor_set(v___x_1201_, 1, v___x_1219_);
                            leanh::lean_ctor_set(v___x_1201_, 0, v___x_1218_);
                            v___x_1221_ = v___x_1201_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1222_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
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
                v___x_1214_ = leanh::lean_unsigned_to_nat(1);
                v___x_1215_ = lean_nat_add(v_x_1195_, v___x_1214_);
                leanh::lean_dec(v_x_1195_);
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
    mut v_n_1224_: *mut leanh::LeanObject,
    mut v_k_1225_: *mut leanh::LeanObject,
    mut v_v_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_1233_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0);
    v___x_1234_ = lean_usize_sub(v___x_1233_, v___x_1232_);
    return v___x_1234_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1235_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(
    mut v_x_1236_: *mut leanh::LeanObject,
    mut v_x_1237_: usize,
    mut v_x_1238_: usize,
    mut v_x_1239_: *mut leanh::LeanObject,
    mut v_x_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v_j_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v_v_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_node_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1277_: usize = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1283_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1285_: u8 = 0;
    let mut v_unused_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1296_: u8 = 0;
    let mut v_ks_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v_reuseFailAlloc_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1236_) == 0 {
                    v_es_1241_ = leanh::lean_ctor_get(v_x_1236_, 0);
                    v___x_1242_ = 5usize;
                    v___x_1243_ = 1usize;
                    v___x_1244_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1);
                    v___x_1245_ = lean_usize_land(v_x_1237_, v___x_1244_);
                    v_j_1246_ = lean_usize_to_nat(v___x_1245_);
                    v___x_1247_ = lean_array_get_size(v_es_1241_);
                    v___x_1248_ = lean_nat_dec_lt(v_j_1246_, v___x_1247_);
                    if v___x_1248_ == 0 {
                        leanh::lean_dec(v_j_1246_);
                        leanh::lean_dec(v_x_1240_);
                        leanh::lean_dec_ref(v_x_1239_);
                        return v_x_1236_;
                    } else {
                        leanh::lean_inc_ref(v_es_1241_);
                        v_isSharedCheck_1285_ = (!leanh::lean_is_exclusive(v_x_1236_)) as u8;
                        if v_isSharedCheck_1285_ == 0 {
                            v_unused_1286_ = leanh::lean_ctor_get(v_x_1236_, 0);
                            leanh::lean_dec(v_unused_1286_);
                            v___x_1250_ = v_x_1236_;
                            v_isShared_1251_ = v_isSharedCheck_1285_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1236_);
                            v___x_1250_ = leanh::lean_box(0);
                            v_isShared_1251_ = v_isSharedCheck_1285_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1287_ = leanh::lean_ctor_get(v_x_1236_, 0);
                    v_vs_1288_ = leanh::lean_ctor_get(v_x_1236_, 1);
                    v_isSharedCheck_1308_ = (!leanh::lean_is_exclusive(v_x_1236_)) as u8;
                    if v_isSharedCheck_1308_ == 0 {
                        v___x_1290_ = v_x_1236_;
                        v_isShared_1291_ = v_isSharedCheck_1308_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1288_);
                        leanh::lean_inc(v_ks_1287_);
                        leanh::lean_dec(v_x_1236_);
                        v___x_1290_ = leanh::lean_box(0);
                        v_isShared_1291_ = v_isSharedCheck_1308_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1252_ = lean_array_fget(v_es_1241_, v_j_1246_);
                v___x_1253_ = leanh::lean_box(0);
                v_xs_x27_1254_ = lean_array_fset(v_es_1241_, v_j_1246_, v___x_1253_);
                match leanh::lean_obj_tag(v_v_1252_) {
                    0 => {
                        v_key_1261_ = leanh::lean_ctor_get(v_v_1252_, 0);
                        v_val_1262_ = leanh::lean_ctor_get(v_v_1252_, 1);
                        v_isSharedCheck_1272_ = (!leanh::lean_is_exclusive(v_v_1252_)) as u8;
                        if v_isSharedCheck_1272_ == 0 {
                            v___x_1264_ = v_v_1252_;
                            v_isShared_1265_ = v_isSharedCheck_1272_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1262_);
                            leanh::lean_inc(v_key_1261_);
                            leanh::lean_dec(v_v_1252_);
                            v___x_1264_ = leanh::lean_box(0);
                            v_isShared_1265_ = v_isSharedCheck_1272_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1273_ = leanh::lean_ctor_get(v_v_1252_, 0);
                        v_isSharedCheck_1283_ = (!leanh::lean_is_exclusive(v_v_1252_)) as u8;
                        if v_isSharedCheck_1283_ == 0 {
                            v___x_1275_ = v_v_1252_;
                            v_isShared_1276_ = v_isSharedCheck_1283_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1273_);
                            leanh::lean_dec(v_v_1252_);
                            v___x_1275_ = leanh::lean_box(0);
                            v_isShared_1276_ = v_isSharedCheck_1283_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1284_, 0, v_x_1239_);
                        leanh::lean_ctor_set(v___x_1284_, 1, v_x_1240_);
                        v___y_1256_ = v___x_1284_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1257_ = lean_array_fset(v_xs_x27_1254_, v_j_1246_, v___y_1256_);
                leanh::lean_dec(v_j_1246_);
                if v_isShared_1251_ == 0 {
                    leanh::lean_ctor_set(v___x_1250_, 0, v___x_1257_);
                    v___x_1259_ = v___x_1250_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
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
                    leanh::lean_del_object(v___x_1264_);
                    v___x_1267_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1261_,
                        v_val_1262_,
                        v_x_1239_,
                        v_x_1240_,
                    );
                    v___x_1268_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
                    v___y_1256_ = v___x_1268_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1262_);
                    leanh::lean_dec(v_key_1261_);
                    if v_isShared_1265_ == 0 {
                        leanh::lean_ctor_set(v___x_1264_, 1, v_x_1240_);
                        leanh::lean_ctor_set(v___x_1264_, 0, v_x_1239_);
                        v___x_1270_ = v___x_1264_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1271_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_x_1239_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_x_1240_);
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
                    leanh::lean_ctor_set(v___x_1275_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1275_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
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
                    v_reuseFailAlloc_1307_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_ks_1287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_vs_1288_);
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
                    v___x_1305_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1306_ = lean_nat_dec_lt(v___x_1304_, v___x_1305_);
                    leanh::lean_dec(v___x_1304_);
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
                    v_ks_1297_ = leanh::lean_ctor_get(v_newNode_1294_, 0);
                    leanh::lean_inc_ref(v_ks_1297_);
                    v_vs_1298_ = leanh::lean_ctor_get(v_newNode_1294_, 1);
                    leanh::lean_inc_ref(v_vs_1298_);
                    leanh::lean_dec_ref(v_newNode_1294_);
                    v___x_1299_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__2);
                    v___x_1301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_x_1238_, v_ks_1297_, v_vs_1298_, v___x_1299_, v___x_1300_);
                    leanh::lean_dec_ref(v_vs_1298_);
                    leanh::lean_dec_ref(v_ks_1297_);
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
    mut v_keys_1310_: *mut leanh::LeanObject,
    mut v_vals_1311_: *mut leanh::LeanObject,
    mut v_i_1312_: *mut leanh::LeanObject,
    mut v_entries_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v_k_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u64 = 0;
    let mut v_h_1319_: usize = 0;
    let mut v___x_1320_: usize = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: usize = 0;
    let mut v___x_1323_: usize = 0;
    let mut v___x_1324_: usize = 0;
    let mut v_h_1325_: usize = 0;
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1314_ = lean_array_get_size(v_keys_1310_);
                v___x_1315_ = lean_nat_dec_lt(v_i_1312_, v___x_1314_);
                if v___x_1315_ == 0 {
                    leanh::lean_dec(v_i_1312_);
                    return v_entries_1313_;
                } else {
                    v_k_1316_ = lean_array_fget_borrowed(v_keys_1310_, v_i_1312_);
                    v_v_1317_ = lean_array_fget_borrowed(v_vals_1311_, v_i_1312_);
                    v___x_1318_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1316_);
                    v_h_1319_ = lean_uint64_to_usize(v___x_1318_);
                    v___x_1320_ = 5usize;
                    v___x_1321_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1322_ = 1usize;
                    v___x_1323_ = lean_usize_sub(v_depth_1309_, v___x_1322_);
                    v___x_1324_ = lean_usize_mul(v___x_1320_, v___x_1323_);
                    v_h_1325_ = lean_usize_shift_right(v_h_1319_, v___x_1324_);
                    v___x_1326_ = lean_nat_add(v_i_1312_, v___x_1321_);
                    leanh::lean_dec(v_i_1312_);
                    leanh::lean_inc(v_v_1317_);
                    leanh::lean_inc(v_k_1316_);
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
    mut v_depth_1329_: *mut leanh::LeanObject,
    mut v_keys_1330_: *mut leanh::LeanObject,
    mut v_vals_1331_: *mut leanh::LeanObject,
    mut v_i_1332_: *mut leanh::LeanObject,
    mut v_entries_1333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1334_: usize = 0;
    let mut v_res_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1334_ = leanh::lean_unbox_usize(v_depth_1329_);
    leanh::lean_dec(v_depth_1329_);
    v_res_1335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1334_, v_keys_1330_, v_vals_1331_, v_i_1332_, v_entries_1333_);
    leanh::lean_dec_ref(v_vals_1331_);
    leanh::lean_dec_ref(v_keys_1330_);
    return v_res_1335_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(
    mut v_x_1336_: *mut leanh::LeanObject,
    mut v_x_1337_: *mut leanh::LeanObject,
    mut v_x_1338_: *mut leanh::LeanObject,
    mut v_x_1339_: *mut leanh::LeanObject,
    mut v_x_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_42469__boxed_1341_: usize = 0;
    let mut v_x_42470__boxed_1342_: usize = 0;
    let mut v_res_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_42469__boxed_1341_ = leanh::lean_unbox_usize(v_x_1337_);
    leanh::lean_dec(v_x_1337_);
    v_x_42470__boxed_1342_ = leanh::lean_unbox_usize(v_x_1338_);
    leanh::lean_dec(v_x_1338_);
    v_res_1343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_1336_, v_x_42469__boxed_1341_, v_x_42470__boxed_1342_, v_x_1339_, v_x_1340_);
    return v_res_1343_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(
    mut v_x_1344_: *mut leanh::LeanObject,
    mut v_x_1345_: *mut leanh::LeanObject,
    mut v_x_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: u64 = 0;
    let mut v___x_1348_: usize = 0;
    let mut v___x_1349_: usize = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1345_);
    v___x_1348_ = lean_uint64_to_usize(v___x_1347_);
    v___x_1349_ = 1usize;
    v___x_1350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_1344_, v___x_1348_, v___x_1349_, v_x_1345_, v_x_1346_);
    return v___x_1350_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(
    mut v_keys_1351_: *mut leanh::LeanObject,
    mut v_vals_1352_: *mut leanh::LeanObject,
    mut v_i_1353_: *mut leanh::LeanObject,
    mut v_k_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1355_ = lean_array_get_size(v_keys_1351_);
                v___x_1356_ = lean_nat_dec_lt(v_i_1353_, v___x_1355_);
                if v___x_1356_ == 0 {
                    leanh::lean_dec(v_i_1353_);
                    v___x_1357_ = leanh::lean_box(0);
                    return v___x_1357_;
                } else {
                    v_k_x27_1358_ = lean_array_fget_borrowed(v_keys_1351_, v_i_1353_);
                    v___x_1359_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1354_,
                            v_k_x27_1358_,
                        );
                    if v___x_1359_ == 0 {
                        v___x_1360_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1361_ = lean_nat_add(v_i_1353_, v___x_1360_);
                        leanh::lean_dec(v_i_1353_);
                        v_i_1353_ = v___x_1361_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1363_ = lean_array_fget_borrowed(v_vals_1352_, v_i_1353_);
                        leanh::lean_dec(v_i_1353_);
                        leanh::lean_inc(v___x_1363_);
                        v___x_1364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1364_, 0, v___x_1363_);
                        return v___x_1364_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_keys_1365_: *mut leanh::LeanObject,
    mut v_vals_1366_: *mut leanh::LeanObject,
    mut v_i_1367_: *mut leanh::LeanObject,
    mut v_k_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1369_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1365_, v_vals_1366_, v_i_1367_, v_k_1368_);
    leanh::lean_dec_ref(v_k_1368_);
    leanh::lean_dec_ref(v_vals_1366_);
    leanh::lean_dec_ref(v_keys_1365_);
    return v_res_1369_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(
    mut v_x_1370_: *mut leanh::LeanObject,
    mut v_x_1371_: usize,
    mut v_x_1372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: usize = 0;
    let mut v___x_1376_: usize = 0;
    let mut v___x_1377_: usize = 0;
    let mut v_j_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: usize = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1370_) == 0 {
                    v_es_1373_ = leanh::lean_ctor_get(v_x_1370_, 0);
                    v___x_1374_ = leanh::lean_box(2);
                    v___x_1375_ = 5usize;
                    v___x_1376_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__1);
                    v___x_1377_ = lean_usize_land(v_x_1371_, v___x_1376_);
                    v_j_1378_ = lean_usize_to_nat(v___x_1377_);
                    v___x_1379_ = lean_array_get_borrowed(v___x_1374_, v_es_1373_, v_j_1378_);
                    leanh::lean_dec(v_j_1378_);
                    match leanh::lean_obj_tag(v___x_1379_) {
                        0 => {
                            v_key_1380_ = leanh::lean_ctor_get(v___x_1379_, 0);
                            v_val_1381_ = leanh::lean_ctor_get(v___x_1379_, 1);
                            v___x_1382_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1372_, v_key_1380_);
                            if v___x_1382_ == 0 {
                                v___x_1383_ = leanh::lean_box(0);
                                return v___x_1383_;
                            } else {
                                leanh::lean_inc(v_val_1381_);
                                v___x_1384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1384_, 0, v_val_1381_);
                                return v___x_1384_;
                            }
                        }
                        1 => {
                            v_node_1385_ = leanh::lean_ctor_get(v___x_1379_, 0);
                            v___x_1386_ = lean_usize_shift_right(v_x_1371_, v___x_1375_);
                            v_x_1370_ = v_node_1385_;
                            v_x_1371_ = v___x_1386_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1388_ = leanh::lean_box(0);
                            return v___x_1388_;
                        }
                    }
                } else {
                    v_ks_1389_ = leanh::lean_ctor_get(v_x_1370_, 0);
                    v_vs_1390_ = leanh::lean_ctor_get(v_x_1370_, 1);
                    v___x_1391_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_ks_1389_, v_vs_1390_, v___x_1391_, v_x_1372_);
                    return v___x_1392_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(
    mut v_x_1393_: *mut leanh::LeanObject,
    mut v_x_1394_: *mut leanh::LeanObject,
    mut v_x_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_42669__boxed_1396_: usize = 0;
    let mut v_res_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_42669__boxed_1396_ = leanh::lean_unbox_usize(v_x_1394_);
    leanh::lean_dec(v_x_1394_);
    v_res_1397_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_1393_, v_x_42669__boxed_1396_, v_x_1395_);
    leanh::lean_dec_ref(v_x_1395_);
    leanh::lean_dec_ref(v_x_1393_);
    return v_res_1397_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v_x_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1400_: u64 = 0;
    let mut v___x_1401_: usize = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1399_);
    v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
    v___x_1402_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_1398_, v___x_1401_, v_x_1399_);
    return v___x_1402_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(
    mut v_x_1403_: *mut leanh::LeanObject,
    mut v_x_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_1403_, v_x_1404_);
    leanh::lean_dec_ref(v_x_1404_);
    leanh::lean_dec_ref(v_x_1403_);
    return v_res_1405_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1;
    v___x_1409_ = l_Lean_stringToMessageData(v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn lean_sym_dsimp(
    mut v_e_u2081_1410_: *mut leanh::LeanObject,
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
    mut v_a_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_a_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_e_u2082_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1450_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1464_: u8 = 0;
    let mut v___y_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1478_: u8 = 0;
    let mut v_fileName_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1491_: u8 = 0;
    let mut v_cancelTk_x3f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1493_: u8 = 0;
    let mut v_inheritedTraceOptions_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___y_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1520_: u8 = 0;
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1524_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1526_: u8 = 0;
    let mut v_e_x27_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1533_: u8 = 0;
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_1538_: u8 = 0;
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut v_done_1540_: u8 = 0;
    let mut v_e_x27_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v_unused_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: u8 = 0;
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_reuseFailAlloc_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1479_ = leanh::lean_ctor_get(v_a_1418_, 0);
                v_fileMap_1480_ = leanh::lean_ctor_get(v_a_1418_, 1);
                v_options_1481_ = leanh::lean_ctor_get(v_a_1418_, 2);
                v_currRecDepth_1482_ = leanh::lean_ctor_get(v_a_1418_, 3);
                v_maxRecDepth_1483_ = leanh::lean_ctor_get(v_a_1418_, 4);
                v_ref_1484_ = leanh::lean_ctor_get(v_a_1418_, 5);
                v_currNamespace_1485_ = leanh::lean_ctor_get(v_a_1418_, 6);
                v_openDecls_1486_ = leanh::lean_ctor_get(v_a_1418_, 7);
                v_initHeartbeats_1487_ = leanh::lean_ctor_get(v_a_1418_, 8);
                v_maxHeartbeats_1488_ = leanh::lean_ctor_get(v_a_1418_, 9);
                v_quotContext_1489_ = leanh::lean_ctor_get(v_a_1418_, 10);
                v_currMacroScope_1490_ = leanh::lean_ctor_get(v_a_1418_, 11);
                v_diag_1491_ = leanh::lean_ctor_get_uint8(
                    v_a_1418_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1492_ = leanh::lean_ctor_get(v_a_1418_, 12);
                v_suppressElabErrors_1493_ = leanh::lean_ctor_get_uint8(
                    v_a_1418_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1494_ = leanh::lean_ctor_get(v_a_1418_, 13);
                v_isSharedCheck_1606_ = (!leanh::lean_is_exclusive(v_a_1418_)) as u8;
                if v_isSharedCheck_1606_ == 0 {
                    v___x_1496_ = v_a_1418_;
                    v_isShared_1497_ = v_isSharedCheck_1606_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_1494_);
                    leanh::lean_inc(v_cancelTk_x3f_1492_);
                    leanh::lean_inc(v_currMacroScope_1490_);
                    leanh::lean_inc(v_quotContext_1489_);
                    leanh::lean_inc(v_maxHeartbeats_1488_);
                    leanh::lean_inc(v_initHeartbeats_1487_);
                    leanh::lean_inc(v_openDecls_1486_);
                    leanh::lean_inc(v_currNamespace_1485_);
                    leanh::lean_inc(v_ref_1484_);
                    leanh::lean_inc(v_maxRecDepth_1483_);
                    leanh::lean_inc(v_currRecDepth_1482_);
                    leanh::lean_inc(v_options_1481_);
                    leanh::lean_inc(v_fileMap_1480_);
                    leanh::lean_inc(v_fileName_1479_);
                    leanh::lean_dec(v_a_1418_);
                    v___x_1496_ = leanh::lean_box(0);
                    v_isShared_1497_ = v_isSharedCheck_1606_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_1424_ = lean_st_ref_take(v___y_1423_);
                v_numSteps_1425_ = leanh::lean_ctor_get(v___x_1424_, 0);
                v_cache_1426_ = leanh::lean_ctor_get(v___x_1424_, 1);
                v_isSharedCheck_1436_ = (!leanh::lean_is_exclusive(v___x_1424_)) as u8;
                if v_isSharedCheck_1436_ == 0 {
                    v___x_1428_ = v___x_1424_;
                    v_isShared_1429_ = v_isSharedCheck_1436_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_1426_);
                    leanh::lean_inc(v_numSteps_1425_);
                    leanh::lean_dec(v___x_1424_);
                    v___x_1428_ = leanh::lean_box(0);
                    v_isShared_1429_ = v_isSharedCheck_1436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_r_1422_);
                v___x_1430_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_cache_1426_, v_e_u2081_1410_, v_r_1422_);
                if v_isShared_1429_ == 0 {
                    leanh::lean_ctor_set(v___x_1428_, 1, v___x_1430_);
                    v___x_1432_ = v___x_1428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_numSteps_1425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1430_);
                    v___x_1432_ = v_reuseFailAlloc_1435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1433_ = lean_st_ref_set(v___y_1423_, v___x_1432_);
                leanh::lean_dec(v___y_1423_);
                v___x_1434_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1434_, 0, v_r_1422_);
                return v___x_1434_;
            }
            4 => {
                leanh::lean_inc(v___y_1441_);
                leanh::lean_inc_ref(v_e_u2082_1438_);
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
                if leanh::lean_obj_tag(v___x_1448_) == 0 {
                    v_a_1449_ = leanh::lean_ctor_get(v___x_1448_, 0);
                    leanh::lean_inc(v_a_1449_);
                    leanh::lean_dec_ref_known(v___x_1448_, 1);
                    if leanh::lean_obj_tag(v_a_1449_) == 0 {
                        v_done_1450_ = leanh::lean_ctor_get_uint8(v_a_1449_, 0 as u32);
                        leanh::lean_dec_ref_known(v_a_1449_, 0);
                        v___x_1451_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1451_, 0, v_e_u2082_1438_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1451_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_done_1450_,
                        );
                        v_r_1422_ = v___x_1451_;
                        v___y_1423_ = v___y_1441_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_u2082_1438_);
                        v_r_1422_ = v_a_1449_;
                        v___y_1423_ = v___y_1441_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1441_);
                    leanh::lean_dec_ref(v_e_u2082_1438_);
                    leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___x_1448_;
                }
            }
            5 => {
                if v_done_1464_ == 0 {
                    leanh::lean_dec_ref(v_a_1462_);
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
                    leanh::lean_dec_ref(v_e_x27_1463_);
                    leanh::lean_dec_ref(v___y_1461_);
                    leanh::lean_dec(v___y_1459_);
                    leanh::lean_dec_ref(v___y_1458_);
                    leanh::lean_dec(v___y_1457_);
                    leanh::lean_dec_ref(v___y_1456_);
                    leanh::lean_dec(v___y_1455_);
                    leanh::lean_dec(v___y_1454_);
                    leanh::lean_dec(v___y_1453_);
                    v_r_1422_ = v_a_1462_;
                    v___y_1423_ = v___y_1460_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                if leanh::lean_obj_tag(v___y_1475_) == 0 {
                    v_a_1476_ = leanh::lean_ctor_get(v___y_1475_, 0);
                    leanh::lean_inc(v_a_1476_);
                    leanh::lean_dec_ref_known(v___y_1475_, 1);
                    if leanh::lean_obj_tag(v_a_1476_) == 0 {
                        leanh::lean_dec_ref(v___y_1474_);
                        leanh::lean_dec(v___y_1472_);
                        leanh::lean_dec(v___y_1471_);
                        leanh::lean_dec_ref(v___y_1470_);
                        leanh::lean_dec_ref(v___y_1469_);
                        leanh::lean_dec(v___y_1468_);
                        leanh::lean_dec(v___y_1467_);
                        leanh::lean_dec(v___y_1466_);
                        v_r_1422_ = v_a_1476_;
                        v___y_1423_ = v___y_1473_;
                        state = 1;
                        continue;
                    } else {
                        v_e_x27_1477_ = leanh::lean_ctor_get(v_a_1476_, 0);
                        leanh::lean_inc_ref(v_e_x27_1477_);
                        v_done_1478_ = leanh::lean_ctor_get_uint8(
                            v_a_1476_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                    leanh::lean_dec_ref(v___y_1474_);
                    leanh::lean_dec(v___y_1473_);
                    leanh::lean_dec(v___y_1472_);
                    leanh::lean_dec(v___y_1471_);
                    leanh::lean_dec_ref(v___y_1470_);
                    leanh::lean_dec_ref(v___y_1469_);
                    leanh::lean_dec(v___y_1468_);
                    leanh::lean_dec(v___y_1467_);
                    leanh::lean_dec(v___y_1466_);
                    leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___y_1475_;
                }
            }
            7 => {
                v___x_1602_ = leanh::lean_unsigned_to_nat(0);
                v___x_1603_ = lean_nat_dec_eq(v_maxRecDepth_1483_, v___x_1602_);
                if v___x_1603_ == 0 {
                    v___x_1604_ = lean_nat_dec_eq(v_currRecDepth_1482_, v_maxRecDepth_1483_);
                    if v___x_1604_ == 0 {
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_1496_);
                        leanh::lean_dec_ref(v_inheritedTraceOptions_1494_);
                        leanh::lean_dec(v_cancelTk_x3f_1492_);
                        leanh::lean_dec(v_currMacroScope_1490_);
                        leanh::lean_dec(v_quotContext_1489_);
                        leanh::lean_dec(v_maxHeartbeats_1488_);
                        leanh::lean_dec(v_initHeartbeats_1487_);
                        leanh::lean_dec(v_openDecls_1486_);
                        leanh::lean_dec(v_currNamespace_1485_);
                        leanh::lean_dec(v_maxRecDepth_1483_);
                        leanh::lean_dec(v_currRecDepth_1482_);
                        leanh::lean_dec_ref(v_options_1481_);
                        leanh::lean_dec_ref(v_fileMap_1480_);
                        leanh::lean_dec_ref(v_fileName_1479_);
                        leanh::lean_dec(v_a_1419_);
                        leanh::lean_dec(v_a_1417_);
                        leanh::lean_dec_ref(v_a_1416_);
                        leanh::lean_dec(v_a_1415_);
                        leanh::lean_dec_ref(v_a_1414_);
                        leanh::lean_dec(v_a_1413_);
                        leanh::lean_dec(v_a_1412_);
                        leanh::lean_dec(v_a_1411_);
                        leanh::lean_dec_ref(v_e_u2081_1410_);
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
                v_cache_1510_ = leanh::lean_ctor_get(v___x_1509_, 1);
                v_isSharedCheck_1543_ = (!leanh::lean_is_exclusive(v___x_1509_)) as u8;
                if v_isSharedCheck_1543_ == 0 {
                    v_unused_1544_ = leanh::lean_ctor_get(v___x_1509_, 0);
                    leanh::lean_dec(v_unused_1544_);
                    v___x_1512_ = v___x_1509_;
                    v_isShared_1513_ = v_isSharedCheck_1543_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_1510_);
                    leanh::lean_dec(v___x_1509_);
                    v___x_1512_ = leanh::lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1543_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1513_ == 0 {
                    leanh::lean_ctor_set(v___x_1512_, 0, v___y_1499_);
                    v___x_1515_ = v___x_1512_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___y_1499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_cache_1510_);
                    v___x_1515_ = v_reuseFailAlloc_1542_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1516_ = lean_st_ref_set(v___y_1502_, v___x_1515_);
                v_pre_1517_ = leanh::lean_ctor_get(v___y_1500_, 0);
                leanh::lean_inc_ref(v_pre_1517_);
                leanh::lean_inc(v___y_1508_);
                leanh::lean_inc_ref(v___y_1507_);
                leanh::lean_inc(v___y_1506_);
                leanh::lean_inc_ref(v___y_1505_);
                leanh::lean_inc(v___y_1504_);
                leanh::lean_inc_ref(v___y_1503_);
                leanh::lean_inc(v___y_1502_);
                leanh::lean_inc(v___y_1501_);
                leanh::lean_inc(v___y_1500_);
                leanh::lean_inc_ref(v_e_u2081_1410_);
                v___x_1518_ = leanh::lean_apply_11(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1518_) == 0 {
                    v_a_1519_ = leanh::lean_ctor_get(v___x_1518_, 0);
                    leanh::lean_inc(v_a_1519_);
                    leanh::lean_dec_ref_known(v___x_1518_, 1);
                    if leanh::lean_obj_tag(v_a_1519_) == 0 {
                        v_done_1520_ = leanh::lean_ctor_get_uint8(v_a_1519_, 0 as u32);
                        if v_done_1520_ == 0 {
                            leanh::lean_dec_ref_known(v_a_1519_, 0);
                            leanh::lean_inc_ref(v_e_u2081_1410_);
                            v___x_1521_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_u2081_1410_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
                            if leanh::lean_obj_tag(v___x_1521_) == 0 {
                                v_a_1522_ = leanh::lean_ctor_get(v___x_1521_, 0);
                                leanh::lean_inc(v_a_1522_);
                                v___x_1523_ = leanh::lean_box(0);
                                if leanh::lean_obj_tag(v_a_1522_) == 0 {
                                    v_done_1524_ =
                                        leanh::lean_ctor_get_uint8(v_a_1522_, 0 as u32);
                                    leanh::lean_dec_ref_known(v_a_1522_, 0);
                                    if v_done_1524_ == 0 {
                                        leanh::lean_dec_ref_known(v___x_1521_, 1);
                                        leanh::lean_inc_ref(v_e_u2081_1410_);
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
                                    v_done_1526_ = leanh::lean_ctor_get_uint8(
                                        v_a_1522_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                            as u32,
                                    );
                                    if v_done_1526_ == 0 {
                                        leanh::lean_dec_ref_known(v___x_1521_, 1);
                                        v_e_x27_1527_ = leanh::lean_ctor_get(v_a_1522_, 0);
                                        v_isSharedCheck_1539_ =
                                            (!leanh::lean_is_exclusive(v_a_1522_)) as u8;
                                        if v_isSharedCheck_1539_ == 0 {
                                            v___x_1529_ = v_a_1522_;
                                            v_isShared_1530_ = v_isSharedCheck_1539_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_e_x27_1527_);
                                            leanh::lean_dec(v_a_1522_);
                                            v___x_1529_ = leanh::lean_box(0);
                                            v_isShared_1530_ = v_isSharedCheck_1539_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_a_1522_, 1);
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
                            leanh::lean_dec(v___y_1508_);
                            leanh::lean_dec_ref(v___y_1507_);
                            leanh::lean_dec(v___y_1506_);
                            leanh::lean_dec_ref(v___y_1505_);
                            leanh::lean_dec(v___y_1504_);
                            leanh::lean_dec_ref(v___y_1503_);
                            leanh::lean_dec(v___y_1501_);
                            leanh::lean_dec(v___y_1500_);
                            v_r_1422_ = v_a_1519_;
                            v___y_1423_ = v___y_1502_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_done_1540_ = leanh::lean_ctor_get_uint8(
                            v_a_1519_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_done_1540_ == 0 {
                            v_e_x27_1541_ = leanh::lean_ctor_get(v_a_1519_, 0);
                            leanh::lean_inc_ref(v_e_x27_1541_);
                            leanh::lean_dec_ref_known(v_a_1519_, 1);
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
                            leanh::lean_dec(v___y_1508_);
                            leanh::lean_dec_ref(v___y_1507_);
                            leanh::lean_dec(v___y_1506_);
                            leanh::lean_dec_ref(v___y_1505_);
                            leanh::lean_dec(v___y_1504_);
                            leanh::lean_dec_ref(v___y_1503_);
                            leanh::lean_dec(v___y_1501_);
                            leanh::lean_dec(v___y_1500_);
                            v_r_1422_ = v_a_1519_;
                            v___y_1423_ = v___y_1502_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1508_);
                    leanh::lean_dec_ref(v___y_1507_);
                    leanh::lean_dec(v___y_1506_);
                    leanh::lean_dec_ref(v___y_1505_);
                    leanh::lean_dec(v___y_1504_);
                    leanh::lean_dec_ref(v___y_1503_);
                    leanh::lean_dec(v___y_1502_);
                    leanh::lean_dec(v___y_1501_);
                    leanh::lean_dec(v___y_1500_);
                    leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___x_1518_;
                }
            }
            11 => {
                leanh::lean_inc_ref(v_e_x27_1527_);
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
                if leanh::lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = leanh::lean_ctor_get(v___x_1531_, 0);
                    leanh::lean_inc(v_a_1532_);
                    leanh::lean_dec_ref_known(v___x_1531_, 1);
                    if leanh::lean_obj_tag(v_a_1532_) == 0 {
                        v_done_1533_ = leanh::lean_ctor_get_uint8(v_a_1532_, 0 as u32);
                        leanh::lean_dec_ref_known(v_a_1532_, 0);
                        leanh::lean_inc_ref(v_e_x27_1527_);
                        if v_isShared_1530_ == 0 {
                            v___x_1535_ = v___x_1529_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1536_ =
                                leanh::lean_alloc_ctor(1, 1, (1) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_e_x27_1527_);
                            v___x_1535_ = v_reuseFailAlloc_1536_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1529_);
                        leanh::lean_dec_ref(v_e_x27_1527_);
                        v_e_x27_1537_ = leanh::lean_ctor_get(v_a_1532_, 0);
                        leanh::lean_inc_ref(v_e_x27_1537_);
                        v_done_1538_ = leanh::lean_ctor_get_uint8(
                            v_a_1532_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                    leanh::lean_del_object(v___x_1529_);
                    leanh::lean_dec_ref(v_e_x27_1527_);
                    leanh::lean_dec(v___y_1508_);
                    leanh::lean_dec_ref(v___y_1507_);
                    leanh::lean_dec(v___y_1506_);
                    leanh::lean_dec_ref(v___y_1505_);
                    leanh::lean_dec(v___y_1504_);
                    leanh::lean_dec_ref(v___y_1503_);
                    leanh::lean_dec(v___y_1502_);
                    leanh::lean_dec(v___y_1501_);
                    leanh::lean_dec(v___y_1500_);
                    leanh::lean_dec_ref(v_e_u2081_1410_);
                    return v___x_1531_;
                }
            }
            12 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1535_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                v_cache_1558_ = leanh::lean_ctor_get(v___x_1557_, 1);
                leanh::lean_inc_ref(v_cache_1558_);
                leanh::lean_dec(v___x_1557_);
                v___x_1559_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_cache_1558_, v_e_u2081_1410_);
                leanh::lean_dec_ref(v_cache_1558_);
                if leanh::lean_obj_tag(v___x_1559_) == 1 {
                    leanh::lean_dec(v___y_1556_);
                    leanh::lean_dec_ref(v___y_1555_);
                    leanh::lean_dec(v___y_1554_);
                    leanh::lean_dec_ref(v___y_1553_);
                    leanh::lean_dec(v___y_1552_);
                    leanh::lean_dec_ref(v___y_1551_);
                    leanh::lean_dec(v___y_1550_);
                    leanh::lean_dec(v___y_1549_);
                    leanh::lean_dec(v___y_1548_);
                    leanh::lean_dec(v___y_1546_);
                    leanh::lean_dec_ref(v_e_u2081_1410_);
                    v_val_1560_ = leanh::lean_ctor_get(v___x_1559_, 0);
                    v_isSharedCheck_1567_ = (!leanh::lean_is_exclusive(v___x_1559_)) as u8;
                    if v_isSharedCheck_1567_ == 0 {
                        v___x_1562_ = v___x_1559_;
                        v_isShared_1563_ = v_isSharedCheck_1567_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1560_);
                        leanh::lean_dec(v___x_1559_);
                        v___x_1562_ = leanh::lean_box(0);
                        v_isShared_1563_ = v_isSharedCheck_1567_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1559_);
                    v___x_1568_ = lean_nat_add(v___y_1546_, v___y_1547_);
                    leanh::lean_dec(v___y_1546_);
                    v___x_1569_ = leanh::lean_unsigned_to_nat(1000);
                    v___x_1570_ = lean_nat_mod(v___x_1568_, v___x_1569_);
                    v___x_1571_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1572_ = lean_nat_dec_eq(v___x_1570_, v___x_1571_);
                    leanh::lean_dec(v___x_1570_);
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
                        if leanh::lean_obj_tag(v___x_1574_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1574_, 1);
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
                            leanh::lean_dec(v___x_1568_);
                            leanh::lean_dec(v___y_1556_);
                            leanh::lean_dec_ref(v___y_1555_);
                            leanh::lean_dec(v___y_1554_);
                            leanh::lean_dec_ref(v___y_1553_);
                            leanh::lean_dec(v___y_1552_);
                            leanh::lean_dec_ref(v___y_1551_);
                            leanh::lean_dec(v___y_1550_);
                            leanh::lean_dec(v___y_1549_);
                            leanh::lean_dec(v___y_1548_);
                            leanh::lean_dec_ref(v_e_u2081_1410_);
                            v_a_1575_ = leanh::lean_ctor_get(v___x_1574_, 0);
                            v_isSharedCheck_1582_ =
                                (!leanh::lean_is_exclusive(v___x_1574_)) as u8;
                            if v_isSharedCheck_1582_ == 0 {
                                v___x_1577_ = v___x_1574_;
                                v_isShared_1578_ = v_isSharedCheck_1582_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1575_);
                                leanh::lean_dec(v___x_1574_);
                                v___x_1577_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set_tag(v___x_1562_, 0);
                    v___x_1565_ = v___x_1562_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1560_);
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
                    v_reuseFailAlloc_1581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
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
                v_numSteps_1585_ = leanh::lean_ctor_get(v___x_1584_, 0);
                leanh::lean_inc(v_numSteps_1585_);
                leanh::lean_dec(v___x_1584_);
                v___x_1586_ = leanh::lean_unsigned_to_nat(1);
                v___x_1587_ = lean_nat_add(v_currRecDepth_1482_, v___x_1586_);
                leanh::lean_dec(v_currRecDepth_1482_);
                if v_isShared_1497_ == 0 {
                    leanh::lean_ctor_set(v___x_1496_, 3, v___x_1587_);
                    v___x_1589_ = v___x_1496_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_fileName_1479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_fileMap_1480_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_options_1481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___x_1587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_maxRecDepth_1483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 5, v_ref_1484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 6, v_currNamespace_1485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 7, v_openDecls_1486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 8, v_initHeartbeats_1487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 9, v_maxHeartbeats_1488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 10, v_quotContext_1489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 11, v_currMacroScope_1490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 12, v_cancelTk_x3f_1492_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1601_,
                        13,
                        v_inheritedTraceOptions_1494_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1601_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_1491_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1601_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
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
                    leanh::lean_dec(v_numSteps_1585_);
                    leanh::lean_dec(v_a_1415_);
                    leanh::lean_dec_ref(v_a_1414_);
                    leanh::lean_dec(v_a_1413_);
                    leanh::lean_dec(v_a_1412_);
                    leanh::lean_dec(v_a_1411_);
                    leanh::lean_dec_ref(v_e_u2081_1410_);
                    v___x_1591_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once), _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2);
                    v___x_1592_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_1591_, v_a_1416_, v_a_1417_, v___x_1589_, v_a_1419_);
                    leanh::lean_dec(v_a_1419_);
                    leanh::lean_dec_ref(v___x_1589_);
                    leanh::lean_dec(v_a_1417_);
                    leanh::lean_dec_ref(v_a_1416_);
                    v_a_1593_ = leanh::lean_ctor_get(v___x_1592_, 0);
                    v_isSharedCheck_1600_ = (!leanh::lean_is_exclusive(v___x_1592_)) as u8;
                    if v_isSharedCheck_1600_ == 0 {
                        v___x_1595_ = v___x_1592_;
                        v_isShared_1596_ = v_isSharedCheck_1600_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1593_);
                        leanh::lean_dec(v___x_1592_);
                        v___x_1595_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
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
    mut v_e_u2081_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
    mut v_a_1609_: *mut leanh::LeanObject,
    mut v_a_1610_: *mut leanh::LeanObject,
    mut v_a_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
    mut v_a_1613_: *mut leanh::LeanObject,
    mut v_a_1614_: *mut leanh::LeanObject,
    mut v_a_1615_: *mut leanh::LeanObject,
    mut v_a_1616_: *mut leanh::LeanObject,
    mut v_a_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b2_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: *mut leanh::LeanObject,
    mut v_x_1621_: *mut leanh::LeanObject,
    mut v_x_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_x_1620_, v_x_1621_, v_x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(
    mut v_00_u03b2_1624_: *mut leanh::LeanObject,
    mut v_x_1625_: *mut leanh::LeanObject,
    mut v_x_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_1625_, v_x_1626_);
    return v___x_1627_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(
    mut v_00_u03b2_1628_: *mut leanh::LeanObject,
    mut v_x_1629_: *mut leanh::LeanObject,
    mut v_x_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(v_00_u03b2_1628_, v_x_1629_, v_x_1630_);
    leanh::lean_dec_ref(v_x_1630_);
    leanh::lean_dec_ref(v_x_1629_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(
    mut v_00_u03b2_1632_: *mut leanh::LeanObject,
    mut v_x_1633_: *mut leanh::LeanObject,
    mut v_x_1634_: usize,
    mut v_x_1635_: usize,
    mut v_x_1636_: *mut leanh::LeanObject,
    mut v_x_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_1633_, v_x_1634_, v_x_1635_, v_x_1636_, v_x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(
    mut v_00_u03b2_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
    mut v_x_1641_: *mut leanh::LeanObject,
    mut v_x_1642_: *mut leanh::LeanObject,
    mut v_x_1643_: *mut leanh::LeanObject,
    mut v_x_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_43095__boxed_1645_: usize = 0;
    let mut v_x_43096__boxed_1646_: usize = 0;
    let mut v_res_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_43095__boxed_1645_ = leanh::lean_unbox_usize(v_x_1641_);
    leanh::lean_dec(v_x_1641_);
    v_x_43096__boxed_1646_ = leanh::lean_unbox_usize(v_x_1642_);
    leanh::lean_dec(v_x_1642_);
    v_res_1647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(v_00_u03b2_1639_, v_x_1640_, v_x_43095__boxed_1645_, v_x_43096__boxed_1646_, v_x_1643_, v_x_1644_);
    return v_res_1647_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(
    mut v_00_u03b2_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
    mut v_x_1650_: usize,
    mut v_x_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_1649_, v_x_1650_, v_x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(
    mut v_00_u03b2_1653_: *mut leanh::LeanObject,
    mut v_x_1654_: *mut leanh::LeanObject,
    mut v_x_1655_: *mut leanh::LeanObject,
    mut v_x_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_43112__boxed_1657_: usize = 0;
    let mut v_res_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_43112__boxed_1657_ = leanh::lean_unbox_usize(v_x_1655_);
    leanh::lean_dec(v_x_1655_);
    v_res_1658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(v_00_u03b2_1653_, v_x_1654_, v_x_43112__boxed_1657_, v_x_1656_);
    leanh::lean_dec_ref(v_x_1656_);
    leanh::lean_dec_ref(v_x_1654_);
    return v_res_1658_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1659_: *mut leanh::LeanObject,
    mut v_n_1660_: *mut leanh::LeanObject,
    mut v_k_1661_: *mut leanh::LeanObject,
    mut v_v_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v_n_1660_, v_k_1661_, v_v_1662_);
    return v___x_1663_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1664_: *mut leanh::LeanObject,
    mut v_depth_1665_: usize,
    mut v_keys_1666_: *mut leanh::LeanObject,
    mut v_vals_1667_: *mut leanh::LeanObject,
    mut v_heq_1668_: *mut leanh::LeanObject,
    mut v_i_1669_: *mut leanh::LeanObject,
    mut v_entries_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_1665_, v_keys_1666_, v_vals_1667_, v_i_1669_, v_entries_1670_);
    return v___x_1671_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_1672_: *mut leanh::LeanObject,
    mut v_depth_1673_: *mut leanh::LeanObject,
    mut v_keys_1674_: *mut leanh::LeanObject,
    mut v_vals_1675_: *mut leanh::LeanObject,
    mut v_heq_1676_: *mut leanh::LeanObject,
    mut v_i_1677_: *mut leanh::LeanObject,
    mut v_entries_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1679_: usize = 0;
    let mut v_res_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1679_ = leanh::lean_unbox_usize(v_depth_1673_);
    leanh::lean_dec(v_depth_1673_);
    v_res_1680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(v_00_u03b2_1672_, v_depth_boxed_1679_, v_keys_1674_, v_vals_1675_, v_heq_1676_, v_i_1677_, v_entries_1678_);
    leanh::lean_dec_ref(v_vals_1675_);
    leanh::lean_dec_ref(v_keys_1674_);
    return v_res_1680_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(
    mut v_00_u03b2_1681_: *mut leanh::LeanObject,
    mut v_keys_1682_: *mut leanh::LeanObject,
    mut v_vals_1683_: *mut leanh::LeanObject,
    mut v_heq_1684_: *mut leanh::LeanObject,
    mut v_i_1685_: *mut leanh::LeanObject,
    mut v_k_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_1682_, v_vals_1683_, v_i_1685_, v_k_1686_);
    return v___x_1687_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_1688_: *mut leanh::LeanObject,
    mut v_keys_1689_: *mut leanh::LeanObject,
    mut v_vals_1690_: *mut leanh::LeanObject,
    mut v_heq_1691_: *mut leanh::LeanObject,
    mut v_i_1692_: *mut leanh::LeanObject,
    mut v_k_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(v_00_u03b2_1688_, v_keys_1689_, v_vals_1690_, v_heq_1691_, v_i_1692_, v_k_1693_);
    leanh::lean_dec_ref(v_k_1693_);
    leanh::lean_dec_ref(v_vals_1690_);
    leanh::lean_dec_ref(v_keys_1689_);
    return v_res_1694_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1695_: *mut leanh::LeanObject,
    mut v_x_1696_: *mut leanh::LeanObject,
    mut v_x_1697_: *mut leanh::LeanObject,
    mut v_x_1698_: *mut leanh::LeanObject,
    mut v_x_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1696_, v_x_1697_, v_x_1698_, v_x_1699_);
    return v___x_1700_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Main(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Main(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Main(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Main(builtin);
}