// Lean compiler output
// Module: Lean.Meta.Sym.LooseBVarsS
// Imports: Lean.Meta.Sym.ReplaceS
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Prelude::{l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_bvar___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_looseBVarRange,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    l_Lean_Meta_Sym_Internal_Builder_assertShared, l_Lean_Meta_Sym_Internal_Builder_share1___redArg,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::ReplaceS::{
    initialize_Lean_Meta_Sym_ReplaceS, l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save,
    runtime_initialize_Lean_Meta_Sym_ReplaceS,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(
    mut v_idx_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lean_Expr_bvar___override(v_idx_1103_);
    v___x_1106_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1105_, v___y_1104_);
    return v___x_1106_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(
    mut v_idx_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: u8,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v_idx_1107_, v___y_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(
    mut v_idx_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21034__boxed_1114_: u8 = 0;
    let mut v_res_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21034__boxed_1114_ = (crate::leanh::lean_unbox(v___y_1112_) as u8);
    v_res_1115_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(
            v_idx_1111_,
            v___y_21034__boxed_1114_,
            v___y_1113_,
        );
    return v_res_1115_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(
    mut v_x_1116_: *mut crate::leanh::LeanObject,
    mut v_bi_1117_: u8,
    mut v_t_1118_: *mut crate::leanh::LeanObject,
    mut v_b_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: u8,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1121_ == 0 {
                    v___y_1124_ = v___y_1120_;
                    v___y_1125_ = v___y_1122_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_1118_);
                    v___x_1138_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1118_,
                        v___y_1121_,
                        v___y_1122_,
                    );
                    v_snd_1139_ = crate::leanh::lean_ctor_get(v___x_1138_, 1);
                    crate::leanh::lean_inc(v_snd_1139_);
                    crate::leanh::lean_dec_ref(v___x_1138_);
                    crate::leanh::lean_inc_ref(v_b_1119_);
                    v___x_1140_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1119_,
                        v___y_1121_,
                        v_snd_1139_,
                    );
                    v_snd_1141_ = crate::leanh::lean_ctor_get(v___x_1140_, 1);
                    crate::leanh::lean_inc(v_snd_1141_);
                    crate::leanh::lean_dec_ref(v___x_1140_);
                    v___y_1124_ = v___y_1120_;
                    v___y_1125_ = v_snd_1141_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1126_ =
                    l_Lean_Expr_forallE___override(v_x_1116_, v_t_1118_, v_b_1119_, v_bi_1117_);
                v___x_1127_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1126_, v___y_1125_);
                v_fst_1128_ = crate::leanh::lean_ctor_get(v___x_1127_, 0);
                v_snd_1129_ = crate::leanh::lean_ctor_get(v___x_1127_, 1);
                v_isSharedCheck_1137_ = (!crate::leanh::lean_is_exclusive(v___x_1127_)) as u8;
                if v_isSharedCheck_1137_ == 0 {
                    v___x_1131_ = v___x_1127_;
                    v_isShared_1132_ = v_isSharedCheck_1137_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1129_);
                    crate::leanh::lean_inc(v_fst_1128_);
                    crate::leanh::lean_dec(v___x_1127_);
                    v___x_1131_ = crate::leanh::lean_box(0);
                    v_isShared_1132_ = v_isSharedCheck_1137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1131_, 1, v___y_1124_);
                    v___x_1134_ = v___x_1131_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_fst_1128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___y_1124_);
                    v___x_1134_ = v_reuseFailAlloc_1136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1135_, 0, v___x_1134_);
                crate::leanh::lean_ctor_set(v___x_1135_, 1, v_snd_1129_);
                return v___x_1135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(
    mut v_x_1142_: *mut crate::leanh::LeanObject,
    mut v_bi_1143_: *mut crate::leanh::LeanObject,
    mut v_t_1144_: *mut crate::leanh::LeanObject,
    mut v_b_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1149_: u8 = 0;
    let mut v___y_21043__boxed_1150_: u8 = 0;
    let mut v_res_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1149_ = (crate::leanh::lean_unbox(v_bi_1143_) as u8);
    v___y_21043__boxed_1150_ = (crate::leanh::lean_unbox(v___y_1147_) as u8);
    v_res_1151_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_1142_, v_bi_boxed_1149_, v_t_1144_, v_b_1145_, v___y_1146_, v___y_21043__boxed_1150_, v___y_1148_);
    return v_res_1151_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(
    mut v_structName_1152_: *mut crate::leanh::LeanObject,
    mut v_idx_1153_: *mut crate::leanh::LeanObject,
    mut v_struct_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: u8,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1172_: u8 = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1156_ == 0 {
                    v___y_1159_ = v___y_1155_;
                    v___y_1160_ = v___y_1157_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_struct_1154_);
                    v___x_1173_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_1154_,
                        v___y_1156_,
                        v___y_1157_,
                    );
                    v_snd_1174_ = crate::leanh::lean_ctor_get(v___x_1173_, 1);
                    crate::leanh::lean_inc(v_snd_1174_);
                    crate::leanh::lean_dec_ref(v___x_1173_);
                    v___y_1159_ = v___y_1155_;
                    v___y_1160_ = v_snd_1174_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1161_ =
                    l_Lean_Expr_proj___override(v_structName_1152_, v_idx_1153_, v_struct_1154_);
                v___x_1162_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1161_, v___y_1160_);
                v_fst_1163_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                v_snd_1164_ = crate::leanh::lean_ctor_get(v___x_1162_, 1);
                v_isSharedCheck_1172_ = (!crate::leanh::lean_is_exclusive(v___x_1162_)) as u8;
                if v_isSharedCheck_1172_ == 0 {
                    v___x_1166_ = v___x_1162_;
                    v_isShared_1167_ = v_isSharedCheck_1172_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1164_);
                    crate::leanh::lean_inc(v_fst_1163_);
                    crate::leanh::lean_dec(v___x_1162_);
                    v___x_1166_ = crate::leanh::lean_box(0);
                    v_isShared_1167_ = v_isSharedCheck_1172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1166_, 1, v___y_1159_);
                    v___x_1169_ = v___x_1166_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_fst_1163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___y_1159_);
                    v___x_1169_ = v_reuseFailAlloc_1171_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                crate::leanh::lean_ctor_set(v___x_1170_, 1, v_snd_1164_);
                return v___x_1170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(
    mut v_structName_1175_: *mut crate::leanh::LeanObject,
    mut v_idx_1176_: *mut crate::leanh::LeanObject,
    mut v_struct_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21092__boxed_1181_: u8 = 0;
    let mut v_res_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21092__boxed_1181_ = (crate::leanh::lean_unbox(v___y_1179_) as u8);
    v_res_1182_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_1175_, v_idx_1176_, v_struct_1177_, v___y_1178_, v___y_21092__boxed_1181_, v___y_1180_);
    return v_res_1182_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(
    mut v_x_1183_: *mut crate::leanh::LeanObject,
    mut v_bi_1184_: u8,
    mut v_t_1185_: *mut crate::leanh::LeanObject,
    mut v_b_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: u8,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1199_: u8 = 0;
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1188_ == 0 {
                    v___y_1191_ = v___y_1187_;
                    v___y_1192_ = v___y_1189_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_1185_);
                    v___x_1205_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1185_,
                        v___y_1188_,
                        v___y_1189_,
                    );
                    v_snd_1206_ = crate::leanh::lean_ctor_get(v___x_1205_, 1);
                    crate::leanh::lean_inc(v_snd_1206_);
                    crate::leanh::lean_dec_ref(v___x_1205_);
                    crate::leanh::lean_inc_ref(v_b_1186_);
                    v___x_1207_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1186_,
                        v___y_1188_,
                        v_snd_1206_,
                    );
                    v_snd_1208_ = crate::leanh::lean_ctor_get(v___x_1207_, 1);
                    crate::leanh::lean_inc(v_snd_1208_);
                    crate::leanh::lean_dec_ref(v___x_1207_);
                    v___y_1191_ = v___y_1187_;
                    v___y_1192_ = v_snd_1208_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1193_ =
                    l_Lean_Expr_lam___override(v_x_1183_, v_t_1185_, v_b_1186_, v_bi_1184_);
                v___x_1194_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1193_, v___y_1192_);
                v_fst_1195_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                v_snd_1196_ = crate::leanh::lean_ctor_get(v___x_1194_, 1);
                v_isSharedCheck_1204_ = (!crate::leanh::lean_is_exclusive(v___x_1194_)) as u8;
                if v_isSharedCheck_1204_ == 0 {
                    v___x_1198_ = v___x_1194_;
                    v_isShared_1199_ = v_isSharedCheck_1204_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1196_);
                    crate::leanh::lean_inc(v_fst_1195_);
                    crate::leanh::lean_dec(v___x_1194_);
                    v___x_1198_ = crate::leanh::lean_box(0);
                    v_isShared_1199_ = v_isSharedCheck_1204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1199_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1198_, 1, v___y_1191_);
                    v___x_1201_ = v___x_1198_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_fst_1195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___y_1191_);
                    v___x_1201_ = v_reuseFailAlloc_1203_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1202_, 0, v___x_1201_);
                crate::leanh::lean_ctor_set(v___x_1202_, 1, v_snd_1196_);
                return v___x_1202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(
    mut v_x_1209_: *mut crate::leanh::LeanObject,
    mut v_bi_1210_: *mut crate::leanh::LeanObject,
    mut v_t_1211_: *mut crate::leanh::LeanObject,
    mut v_b_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1216_: u8 = 0;
    let mut v___y_21136__boxed_1217_: u8 = 0;
    let mut v_res_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1216_ = (crate::leanh::lean_unbox(v_bi_1210_) as u8);
    v___y_21136__boxed_1217_ = (crate::leanh::lean_unbox(v___y_1214_) as u8);
    v_res_1218_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_1209_, v_bi_boxed_1216_, v_t_1211_, v_b_1212_, v___y_1213_, v___y_21136__boxed_1217_, v___y_1215_);
    return v_res_1218_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(
    mut v_msg_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: u8,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20767__overap_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1230_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0;
    v___f_1231_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1;
    v___f_1232_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2;
    v___f_1233_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3;
    v___f_1234_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4;
    v___f_1235_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5;
    v___f_1236_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6;
    v___x_1237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1237_, 0, v___f_1230_);
    crate::leanh::lean_ctor_set(v___x_1237_, 1, v___f_1231_);
    v___x_1238_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    crate::leanh::lean_ctor_set(v___x_1238_, 1, v___f_1232_);
    crate::leanh::lean_ctor_set(v___x_1238_, 2, v___f_1233_);
    crate::leanh::lean_ctor_set(v___x_1238_, 3, v___f_1234_);
    crate::leanh::lean_ctor_set(v___x_1238_, 4, v___f_1235_);
    v___x_1239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    crate::leanh::lean_ctor_set(v___x_1239_, 1, v___f_1236_);
    crate::leanh::lean_inc_ref_n(v___x_1239_, 6);
    v___f_1240_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1240_, 0, v___x_1239_);
    v___f_1241_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1241_, 0, v___x_1239_);
    v___f_1242_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1242_, 0, v___x_1239_);
    v___f_1243_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1243_, 0, v___x_1239_);
    v___x_1244_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1244_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1244_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1244_, 2, v___x_1239_);
    v___x_1245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1245_, 0, v___x_1244_);
    crate::leanh::lean_ctor_set(v___x_1245_, 1, v___f_1240_);
    v___x_1246_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1246_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1246_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1246_, 2, v___x_1239_);
    v___x_1247_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1247_, 0, v___x_1245_);
    crate::leanh::lean_ctor_set(v___x_1247_, 1, v___x_1246_);
    crate::leanh::lean_ctor_set(v___x_1247_, 2, v___f_1241_);
    crate::leanh::lean_ctor_set(v___x_1247_, 3, v___f_1242_);
    crate::leanh::lean_ctor_set(v___x_1247_, 4, v___f_1243_);
    v___x_1248_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1248_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1248_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1248_, 2, v___x_1239_);
    v___x_1249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1247_);
    crate::leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
    v___x_1250_ = l_ReaderT_instMonad___redArg(v___x_1249_);
    crate::leanh::lean_inc_ref_n(v___x_1250_, 6);
    v___f_1251_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1251_, 0, v___x_1250_);
    v___f_1252_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1252_, 0, v___x_1250_);
    v___f_1253_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1253_, 0, v___x_1250_);
    v___f_1254_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1254_, 0, v___x_1250_);
    v___x_1255_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1255_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1255_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1255_, 2, v___x_1250_);
    v___x_1256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1255_);
    crate::leanh::lean_ctor_set(v___x_1256_, 1, v___f_1251_);
    v___x_1257_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1257_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1257_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1257_, 2, v___x_1250_);
    v___x_1258_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1256_);
    crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1257_);
    crate::leanh::lean_ctor_set(v___x_1258_, 2, v___f_1252_);
    crate::leanh::lean_ctor_set(v___x_1258_, 3, v___f_1253_);
    crate::leanh::lean_ctor_set(v___x_1258_, 4, v___f_1254_);
    v___x_1259_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1259_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1259_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1259_, 2, v___x_1250_);
    v___x_1260_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1260_, 0, v___x_1258_);
    crate::leanh::lean_ctor_set(v___x_1260_, 1, v___x_1259_);
    v___x_1261_ = l_Lean_instInhabitedExpr;
    v___x_1262_ = l_instInhabitedOfMonad___redArg(v___x_1260_, v___x_1261_);
    v___x_20767__overap_1263_ = lean_panic_fn_borrowed(v___x_1262_, v_msg_1226_);
    crate::leanh::lean_dec(v___x_1262_);
    v___x_1264_ = crate::leanh::lean_box((v___y_1228_) as usize);
    v___x_1265_ = crate::leanh::lean_apply_3(
        v___x_20767__overap_1263_,
        v___y_1227_,
        v___x_1264_,
        v___y_1229_,
    );
    return v___x_1265_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(
    mut v_msg_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21199__boxed_1270_: u8 = 0;
    let mut v_res_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21199__boxed_1270_ = (crate::leanh::lean_unbox(v___y_1268_) as u8);
    v_res_1271_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_1266_, v___y_1267_, v___y_21199__boxed_1270_, v___y_1269_);
    return v_res_1271_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(
    mut v_f_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: u8,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1275_ == 0 {
                    v___y_1278_ = v___y_1274_;
                    v___y_1279_ = v___y_1276_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_1272_);
                    v___x_1292_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_1272_,
                        v___y_1275_,
                        v___y_1276_,
                    );
                    v_snd_1293_ = crate::leanh::lean_ctor_get(v___x_1292_, 1);
                    crate::leanh::lean_inc(v_snd_1293_);
                    crate::leanh::lean_dec_ref(v___x_1292_);
                    crate::leanh::lean_inc_ref(v_a_1273_);
                    v___x_1294_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_1273_,
                        v___y_1275_,
                        v_snd_1293_,
                    );
                    v_snd_1295_ = crate::leanh::lean_ctor_get(v___x_1294_, 1);
                    crate::leanh::lean_inc(v_snd_1295_);
                    crate::leanh::lean_dec_ref(v___x_1294_);
                    v___y_1278_ = v___y_1274_;
                    v___y_1279_ = v_snd_1295_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1280_ = l_Lean_Expr_app___override(v_f_1272_, v_a_1273_);
                v___x_1281_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1280_, v___y_1279_);
                v_fst_1282_ = crate::leanh::lean_ctor_get(v___x_1281_, 0);
                v_snd_1283_ = crate::leanh::lean_ctor_get(v___x_1281_, 1);
                v_isSharedCheck_1291_ = (!crate::leanh::lean_is_exclusive(v___x_1281_)) as u8;
                if v_isSharedCheck_1291_ == 0 {
                    v___x_1285_ = v___x_1281_;
                    v_isShared_1286_ = v_isSharedCheck_1291_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1283_);
                    crate::leanh::lean_inc(v_fst_1282_);
                    crate::leanh::lean_dec(v___x_1281_);
                    v___x_1285_ = crate::leanh::lean_box(0);
                    v_isShared_1286_ = v_isSharedCheck_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1286_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1285_, 1, v___y_1278_);
                    v___x_1288_ = v___x_1285_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_fst_1282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___y_1278_);
                    v___x_1288_ = v_reuseFailAlloc_1290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1288_);
                crate::leanh::lean_ctor_set(v___x_1289_, 1, v_snd_1283_);
                return v___x_1289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(
    mut v_f_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21285__boxed_1301_: u8 = 0;
    let mut v_res_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21285__boxed_1301_ = (crate::leanh::lean_unbox(v___y_1299_) as u8);
    v_res_1302_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_1296_, v_a_1297_, v___y_1298_, v___y_21285__boxed_1301_, v___y_1300_);
    return v_res_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(
    mut v_a_1303_: *mut crate::leanh::LeanObject,
    mut v_x_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1310_: u8 = 0;
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1304_) == 0 {
                    v___x_1305_ = crate::leanh::lean_box(0);
                    return v___x_1305_;
                } else {
                    v_key_1306_ = crate::leanh::lean_ctor_get(v_x_1304_, 0);
                    v_value_1307_ = crate::leanh::lean_ctor_get(v_x_1304_, 1);
                    v_tail_1308_ = crate::leanh::lean_ctor_get(v_x_1304_, 2);
                    v_fst_1313_ = crate::leanh::lean_ctor_get(v_key_1306_, 0);
                    v_snd_1314_ = crate::leanh::lean_ctor_get(v_key_1306_, 1);
                    v_fst_1315_ = crate::leanh::lean_ctor_get(v_a_1303_, 0);
                    v_snd_1316_ = crate::leanh::lean_ctor_get(v_a_1303_, 1);
                    v___x_1317_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_1313_,
                            v_fst_1315_,
                        );
                    if v___x_1317_ == 0 {
                        v___y_1310_ = v___x_1317_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1318_ = lean_nat_dec_eq(v_snd_1314_, v_snd_1316_);
                        v___y_1310_ = v___x_1318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1310_ == 0 {
                    v_x_1304_ = v_tail_1308_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_1307_);
                    v___x_1312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1312_, 0, v_value_1307_);
                    return v___x_1312_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_1319_, v_x_1320_);
    crate::leanh::lean_dec(v_x_1320_);
    crate::leanh::lean_dec_ref(v_a_1319_);
    return v_res_1321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(
    mut v_m_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u64 = 0;
    let mut v___x_1329_: u64 = 0;
    let mut v___x_1330_: u64 = 0;
    let mut v___x_1331_: u64 = 0;
    let mut v___x_1332_: u64 = 0;
    let mut v_fold_1333_: u64 = 0;
    let mut v___x_1334_: u64 = 0;
    let mut v___x_1335_: u64 = 0;
    let mut v___x_1336_: u64 = 0;
    let mut v___x_1337_: usize = 0;
    let mut v___x_1338_: usize = 0;
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: usize = 0;
    let mut v___x_1341_: usize = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1324_ = crate::leanh::lean_ctor_get(v_m_1322_, 1);
    v_fst_1325_ = crate::leanh::lean_ctor_get(v_a_1323_, 0);
    v_snd_1326_ = crate::leanh::lean_ctor_get(v_a_1323_, 1);
    v___x_1327_ = lean_array_get_size(v_buckets_1324_);
    v___x_1328_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1325_);
    v___x_1329_ = lean_uint64_of_nat(v_snd_1326_);
    v___x_1330_ = lean_uint64_mix_hash(v___x_1328_, v___x_1329_);
    v___x_1331_ = 32u64;
    v___x_1332_ = lean_uint64_shift_right(v___x_1330_, v___x_1331_);
    v_fold_1333_ = lean_uint64_xor(v___x_1330_, v___x_1332_);
    v___x_1334_ = 16u64;
    v___x_1335_ = lean_uint64_shift_right(v_fold_1333_, v___x_1334_);
    v___x_1336_ = lean_uint64_xor(v_fold_1333_, v___x_1335_);
    v___x_1337_ = lean_uint64_to_usize(v___x_1336_);
    v___x_1338_ = lean_usize_of_nat(v___x_1327_);
    v___x_1339_ = 1usize;
    v___x_1340_ = lean_usize_sub(v___x_1338_, v___x_1339_);
    v___x_1341_ = lean_usize_land(v___x_1337_, v___x_1340_);
    v___x_1342_ = lean_array_uget_borrowed(v_buckets_1324_, v___x_1341_);
    v___x_1343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_1323_, v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_m_1344_: *mut crate::leanh::LeanObject,
    mut v_a_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_1344_, v_a_1345_);
    crate::leanh::lean_dec_ref(v_a_1345_);
    crate::leanh::lean_dec_ref(v_m_1344_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(
    mut v_x_1347_: *mut crate::leanh::LeanObject,
    mut v_t_1348_: *mut crate::leanh::LeanObject,
    mut v_v_1349_: *mut crate::leanh::LeanObject,
    mut v_b_1350_: *mut crate::leanh::LeanObject,
    mut v_nondep_1351_: u8,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: u8,
    mut v___y_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1369_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1353_ == 0 {
                    v___y_1356_ = v___y_1352_;
                    v___y_1357_ = v___y_1354_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_1348_);
                    v___x_1370_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1348_,
                        v___y_1353_,
                        v___y_1354_,
                    );
                    v_snd_1371_ = crate::leanh::lean_ctor_get(v___x_1370_, 1);
                    crate::leanh::lean_inc(v_snd_1371_);
                    crate::leanh::lean_dec_ref(v___x_1370_);
                    crate::leanh::lean_inc_ref(v_v_1349_);
                    v___x_1372_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_1349_,
                        v___y_1353_,
                        v_snd_1371_,
                    );
                    v_snd_1373_ = crate::leanh::lean_ctor_get(v___x_1372_, 1);
                    crate::leanh::lean_inc(v_snd_1373_);
                    crate::leanh::lean_dec_ref(v___x_1372_);
                    crate::leanh::lean_inc_ref(v_b_1350_);
                    v___x_1374_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1350_,
                        v___y_1353_,
                        v_snd_1373_,
                    );
                    v_snd_1375_ = crate::leanh::lean_ctor_get(v___x_1374_, 1);
                    crate::leanh::lean_inc(v_snd_1375_);
                    crate::leanh::lean_dec_ref(v___x_1374_);
                    v___y_1356_ = v___y_1352_;
                    v___y_1357_ = v_snd_1375_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1358_ = l_Lean_Expr_letE___override(
                    v_x_1347_,
                    v_t_1348_,
                    v_v_1349_,
                    v_b_1350_,
                    v_nondep_1351_,
                );
                v___x_1359_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1358_, v___y_1357_);
                v_fst_1360_ = crate::leanh::lean_ctor_get(v___x_1359_, 0);
                v_snd_1361_ = crate::leanh::lean_ctor_get(v___x_1359_, 1);
                v_isSharedCheck_1369_ = (!crate::leanh::lean_is_exclusive(v___x_1359_)) as u8;
                if v_isSharedCheck_1369_ == 0 {
                    v___x_1363_ = v___x_1359_;
                    v_isShared_1364_ = v_isSharedCheck_1369_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1361_);
                    crate::leanh::lean_inc(v_fst_1360_);
                    crate::leanh::lean_dec(v___x_1359_);
                    v___x_1363_ = crate::leanh::lean_box(0);
                    v_isShared_1364_ = v_isSharedCheck_1369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1364_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1363_, 1, v___y_1356_);
                    v___x_1366_ = v___x_1363_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___y_1356_);
                    v___x_1366_ = v_reuseFailAlloc_1368_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1367_, 0, v___x_1366_);
                crate::leanh::lean_ctor_set(v___x_1367_, 1, v_snd_1361_);
                return v___x_1367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(
    mut v_x_1376_: *mut crate::leanh::LeanObject,
    mut v_t_1377_: *mut crate::leanh::LeanObject,
    mut v_v_1378_: *mut crate::leanh::LeanObject,
    mut v_b_1379_: *mut crate::leanh::LeanObject,
    mut v_nondep_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_1384_: u8 = 0;
    let mut v___y_21403__boxed_1385_: u8 = 0;
    let mut v_res_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_1384_ = (crate::leanh::lean_unbox(v_nondep_1380_) as u8);
    v___y_21403__boxed_1385_ = (crate::leanh::lean_unbox(v___y_1382_) as u8);
    v_res_1386_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_1376_, v_t_1377_, v_v_1378_, v_b_1379_, v_nondep_boxed_1384_, v___y_1381_, v___y_21403__boxed_1385_, v___y_1383_);
    return v_res_1386_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(
    mut v_d_1387_: *mut crate::leanh::LeanObject,
    mut v_e_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: u8,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1390_ == 0 {
                    v___y_1393_ = v___y_1389_;
                    v___y_1394_ = v___y_1391_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_e_1388_);
                    v___x_1407_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_1388_,
                        v___y_1390_,
                        v___y_1391_,
                    );
                    v_snd_1408_ = crate::leanh::lean_ctor_get(v___x_1407_, 1);
                    crate::leanh::lean_inc(v_snd_1408_);
                    crate::leanh::lean_dec_ref(v___x_1407_);
                    v___y_1393_ = v___y_1389_;
                    v___y_1394_ = v_snd_1408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1395_ = l_Lean_Expr_mdata___override(v_d_1387_, v_e_1388_);
                v___x_1396_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1395_, v___y_1394_);
                v_fst_1397_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                v_snd_1398_ = crate::leanh::lean_ctor_get(v___x_1396_, 1);
                v_isSharedCheck_1406_ = (!crate::leanh::lean_is_exclusive(v___x_1396_)) as u8;
                if v_isSharedCheck_1406_ == 0 {
                    v___x_1400_ = v___x_1396_;
                    v_isShared_1401_ = v_isSharedCheck_1406_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1398_);
                    crate::leanh::lean_inc(v_fst_1397_);
                    crate::leanh::lean_dec(v___x_1396_);
                    v___x_1400_ = crate::leanh::lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 1, v___y_1393_);
                    v___x_1403_ = v___x_1400_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_fst_1397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___y_1393_);
                    v___x_1403_ = v_reuseFailAlloc_1405_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
                crate::leanh::lean_ctor_set(v___x_1404_, 1, v_snd_1398_);
                return v___x_1404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(
    mut v_d_1409_: *mut crate::leanh::LeanObject,
    mut v_e_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21457__boxed_1414_: u8 = 0;
    let mut v_res_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21457__boxed_1414_ = (crate::leanh::lean_unbox(v___y_1412_) as u8);
    v_res_1415_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_1409_, v_e_1410_, v___y_1411_, v___y_21457__boxed_1414_, v___y_1413_);
    return v_res_1415_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2;
    v___x_1420_ = crate::leanh::lean_unsigned_to_nat(67);
    v___x_1421_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_1422_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1;
    v___x_1423_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0;
    v___x_1424_ = l_mkPanicMessageWithDecl(
        v___x_1423_,
        v___x_1422_,
        v___x_1421_,
        v___x_1420_,
        v___x_1419_,
    );
    return v___x_1424_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(
    mut v_s_1425_: *mut crate::leanh::LeanObject,
    mut v_d_1426_: *mut crate::leanh::LeanObject,
    mut v_e_1427_: *mut crate::leanh::LeanObject,
    mut v_offset_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: u8,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v_fst_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___y_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_binderName_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1466_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v_fst_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___y_1486_: u8 = 0;
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1495_: u8 = 0;
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v_binderName_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1501_: u8 = 0;
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v_fst_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___y_1521_: u8 = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: u8 = 0;
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_isSharedCheck_1532_: u8 = 0;
    let mut v_declName_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1537_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_fst_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___y_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: u8 = 0;
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut v_data_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v_fst_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_typeName_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v_fst_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_1427_) {
                5 => {
                    v_fn_1432_ = crate::leanh::lean_ctor_get(v_e_1427_, 0);
                    v_arg_1433_ = crate::leanh::lean_ctor_get(v_e_1427_, 1);
                    crate::leanh::lean_inc(v_offset_1428_);
                    crate::leanh::lean_inc_ref(v_fn_1432_);
                    v___x_1434_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_fn_1432_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1435_ = crate::leanh::lean_ctor_get(v___x_1434_, 0);
                    crate::leanh::lean_inc(v_fst_1435_);
                    v_snd_1436_ = crate::leanh::lean_ctor_get(v___x_1434_, 1);
                    crate::leanh::lean_inc(v_snd_1436_);
                    crate::leanh::lean_dec_ref(v___x_1434_);
                    v_fst_1437_ = crate::leanh::lean_ctor_get(v_fst_1435_, 0);
                    crate::leanh::lean_inc(v_fst_1437_);
                    v_snd_1438_ = crate::leanh::lean_ctor_get(v_fst_1435_, 1);
                    crate::leanh::lean_inc(v_snd_1438_);
                    crate::leanh::lean_dec(v_fst_1435_);
                    crate::leanh::lean_inc_ref(v_arg_1433_);
                    v___x_1439_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_arg_1433_, v_offset_1428_, v_snd_1438_, v_a_1430_, v_snd_1436_);
                    v_fst_1440_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    v_snd_1441_ = crate::leanh::lean_ctor_get(v___x_1439_, 1);
                    v_isSharedCheck_1462_ = (!crate::leanh::lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1443_ = v___x_1439_;
                        v_isShared_1444_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1441_);
                        crate::leanh::lean_inc(v_fst_1440_);
                        crate::leanh::lean_dec(v___x_1439_);
                        v___x_1443_ = crate::leanh::lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_1463_ = crate::leanh::lean_ctor_get(v_e_1427_, 0);
                    v_binderType_1464_ = crate::leanh::lean_ctor_get(v_e_1427_, 1);
                    v_body_1465_ = crate::leanh::lean_ctor_get(v_e_1427_, 2);
                    v_binderInfo_1466_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1427_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_1428_);
                    crate::leanh::lean_inc_ref(v_binderType_1464_);
                    v___x_1467_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_binderType_1464_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1468_ = crate::leanh::lean_ctor_get(v___x_1467_, 0);
                    crate::leanh::lean_inc(v_fst_1468_);
                    v_snd_1469_ = crate::leanh::lean_ctor_get(v___x_1467_, 1);
                    crate::leanh::lean_inc(v_snd_1469_);
                    crate::leanh::lean_dec_ref(v___x_1467_);
                    v_fst_1470_ = crate::leanh::lean_ctor_get(v_fst_1468_, 0);
                    crate::leanh::lean_inc(v_fst_1470_);
                    v_snd_1471_ = crate::leanh::lean_ctor_get(v_fst_1468_, 1);
                    crate::leanh::lean_inc(v_snd_1471_);
                    crate::leanh::lean_dec(v_fst_1468_);
                    v___x_1472_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1473_ = lean_nat_add(v_offset_1428_, v___x_1472_);
                    crate::leanh::lean_dec(v_offset_1428_);
                    crate::leanh::lean_inc_ref(v_body_1465_);
                    v___x_1474_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_body_1465_, v___x_1473_, v_snd_1471_, v_a_1430_, v_snd_1469_);
                    v_fst_1475_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                    v_snd_1476_ = crate::leanh::lean_ctor_get(v___x_1474_, 1);
                    v_isSharedCheck_1497_ = (!crate::leanh::lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1478_ = v___x_1474_;
                        v_isShared_1479_ = v_isSharedCheck_1497_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1476_);
                        crate::leanh::lean_inc(v_fst_1475_);
                        crate::leanh::lean_dec(v___x_1474_);
                        v___x_1478_ = crate::leanh::lean_box(0);
                        v_isShared_1479_ = v_isSharedCheck_1497_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_1498_ = crate::leanh::lean_ctor_get(v_e_1427_, 0);
                    v_binderType_1499_ = crate::leanh::lean_ctor_get(v_e_1427_, 1);
                    v_body_1500_ = crate::leanh::lean_ctor_get(v_e_1427_, 2);
                    v_binderInfo_1501_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1427_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_1428_);
                    crate::leanh::lean_inc_ref(v_binderType_1499_);
                    v___x_1502_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_binderType_1499_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1503_ = crate::leanh::lean_ctor_get(v___x_1502_, 0);
                    crate::leanh::lean_inc(v_fst_1503_);
                    v_snd_1504_ = crate::leanh::lean_ctor_get(v___x_1502_, 1);
                    crate::leanh::lean_inc(v_snd_1504_);
                    crate::leanh::lean_dec_ref(v___x_1502_);
                    v_fst_1505_ = crate::leanh::lean_ctor_get(v_fst_1503_, 0);
                    crate::leanh::lean_inc(v_fst_1505_);
                    v_snd_1506_ = crate::leanh::lean_ctor_get(v_fst_1503_, 1);
                    crate::leanh::lean_inc(v_snd_1506_);
                    crate::leanh::lean_dec(v_fst_1503_);
                    v___x_1507_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1508_ = lean_nat_add(v_offset_1428_, v___x_1507_);
                    crate::leanh::lean_dec(v_offset_1428_);
                    crate::leanh::lean_inc_ref(v_body_1500_);
                    v___x_1509_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_body_1500_, v___x_1508_, v_snd_1506_, v_a_1430_, v_snd_1504_);
                    v_fst_1510_ = crate::leanh::lean_ctor_get(v___x_1509_, 0);
                    v_snd_1511_ = crate::leanh::lean_ctor_get(v___x_1509_, 1);
                    v_isSharedCheck_1532_ = (!crate::leanh::lean_is_exclusive(v___x_1509_)) as u8;
                    if v_isSharedCheck_1532_ == 0 {
                        v___x_1513_ = v___x_1509_;
                        v_isShared_1514_ = v_isSharedCheck_1532_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1511_);
                        crate::leanh::lean_inc(v_fst_1510_);
                        crate::leanh::lean_dec(v___x_1509_);
                        v___x_1513_ = crate::leanh::lean_box(0);
                        v_isShared_1514_ = v_isSharedCheck_1532_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_1533_ = crate::leanh::lean_ctor_get(v_e_1427_, 0);
                    v_type_1534_ = crate::leanh::lean_ctor_get(v_e_1427_, 1);
                    v_value_1535_ = crate::leanh::lean_ctor_get(v_e_1427_, 2);
                    v_body_1536_ = crate::leanh::lean_ctor_get(v_e_1427_, 3);
                    v_nondep_1537_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1427_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_n(v_offset_1428_, 2);
                    crate::leanh::lean_inc_ref(v_type_1534_);
                    v___x_1538_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_type_1534_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1539_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    crate::leanh::lean_inc(v_fst_1539_);
                    v_snd_1540_ = crate::leanh::lean_ctor_get(v___x_1538_, 1);
                    crate::leanh::lean_inc(v_snd_1540_);
                    crate::leanh::lean_dec_ref(v___x_1538_);
                    v_fst_1541_ = crate::leanh::lean_ctor_get(v_fst_1539_, 0);
                    crate::leanh::lean_inc(v_fst_1541_);
                    v_snd_1542_ = crate::leanh::lean_ctor_get(v_fst_1539_, 1);
                    crate::leanh::lean_inc(v_snd_1542_);
                    crate::leanh::lean_dec(v_fst_1539_);
                    crate::leanh::lean_inc_ref(v_value_1535_);
                    v___x_1543_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_value_1535_, v_offset_1428_, v_snd_1542_, v_a_1430_, v_snd_1540_);
                    v_fst_1544_ = crate::leanh::lean_ctor_get(v___x_1543_, 0);
                    crate::leanh::lean_inc(v_fst_1544_);
                    v_snd_1545_ = crate::leanh::lean_ctor_get(v___x_1543_, 1);
                    crate::leanh::lean_inc(v_snd_1545_);
                    crate::leanh::lean_dec_ref(v___x_1543_);
                    v_fst_1546_ = crate::leanh::lean_ctor_get(v_fst_1544_, 0);
                    crate::leanh::lean_inc(v_fst_1546_);
                    v_snd_1547_ = crate::leanh::lean_ctor_get(v_fst_1544_, 1);
                    crate::leanh::lean_inc(v_snd_1547_);
                    crate::leanh::lean_dec(v_fst_1544_);
                    v___x_1548_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1549_ = lean_nat_add(v_offset_1428_, v___x_1548_);
                    crate::leanh::lean_dec(v_offset_1428_);
                    crate::leanh::lean_inc_ref(v_body_1536_);
                    v___x_1550_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_body_1536_, v___x_1549_, v_snd_1547_, v_a_1430_, v_snd_1545_);
                    v_fst_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    v_snd_1552_ = crate::leanh::lean_ctor_get(v___x_1550_, 1);
                    v_isSharedCheck_1575_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1575_ == 0 {
                        v___x_1554_ = v___x_1550_;
                        v_isShared_1555_ = v_isSharedCheck_1575_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1552_);
                        crate::leanh::lean_inc(v_fst_1551_);
                        crate::leanh::lean_dec(v___x_1550_);
                        v___x_1554_ = crate::leanh::lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1575_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_1576_ = crate::leanh::lean_ctor_get(v_e_1427_, 0);
                    v_expr_1577_ = crate::leanh::lean_ctor_get(v_e_1427_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1577_);
                    v___x_1578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_expr_1577_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1579_ = crate::leanh::lean_ctor_get(v___x_1578_, 0);
                    v_snd_1580_ = crate::leanh::lean_ctor_get(v___x_1578_, 1);
                    v_isSharedCheck_1598_ = (!crate::leanh::lean_is_exclusive(v___x_1578_)) as u8;
                    if v_isSharedCheck_1598_ == 0 {
                        v___x_1582_ = v___x_1578_;
                        v_isShared_1583_ = v_isSharedCheck_1598_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1580_);
                        crate::leanh::lean_inc(v_fst_1579_);
                        crate::leanh::lean_dec(v___x_1578_);
                        v___x_1582_ = crate::leanh::lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1598_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_1599_ = crate::leanh::lean_ctor_get(v_e_1427_, 0);
                    v_idx_1600_ = crate::leanh::lean_ctor_get(v_e_1427_, 1);
                    v_struct_1601_ = crate::leanh::lean_ctor_get(v_e_1427_, 2);
                    crate::leanh::lean_inc_ref(v_struct_1601_);
                    v___x_1602_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_struct_1601_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1603_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                    v_snd_1604_ = crate::leanh::lean_ctor_get(v___x_1602_, 1);
                    v_isSharedCheck_1622_ = (!crate::leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1622_ == 0 {
                        v___x_1606_ = v___x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1622_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1604_);
                        crate::leanh::lean_inc(v_fst_1603_);
                        crate::leanh::lean_dec(v___x_1602_);
                        v___x_1606_ = crate::leanh::lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1622_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_offset_1428_);
                    crate::leanh::lean_dec_ref(v_e_1427_);
                    v___x_1623_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
                    v___x_1624_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1623_, v_a_1429_, v_a_1430_, v_a_1431_);
                    return v___x_1624_;
                }
            },
            1 => {
                v_fst_1445_ = crate::leanh::lean_ctor_get(v_fst_1440_, 0);
                v_snd_1446_ = crate::leanh::lean_ctor_get(v_fst_1440_, 1);
                v_isSharedCheck_1461_ = (!crate::leanh::lean_is_exclusive(v_fst_1440_)) as u8;
                if v_isSharedCheck_1461_ == 0 {
                    v___x_1448_ = v_fst_1440_;
                    v_isShared_1449_ = v_isSharedCheck_1461_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1446_);
                    crate::leanh::lean_inc(v_fst_1445_);
                    crate::leanh::lean_dec(v_fst_1440_);
                    v___x_1448_ = crate::leanh::lean_box(0);
                    v_isShared_1449_ = v_isSharedCheck_1461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1459_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_1432_,
                        v_fst_1437_,
                    );
                if v___x_1459_ == 0 {
                    v___y_1451_ = v___x_1459_;
                    state = 3;
                    continue;
                } else {
                    v___x_1460_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_1433_,
                            v_fst_1445_,
                        );
                    v___y_1451_ = v___x_1460_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_1451_ == 0 {
                    crate::leanh::lean_del_object(v___x_1448_);
                    crate::leanh::lean_del_object(v___x_1443_);
                    crate::leanh::lean_dec_ref_known(v_e_1427_, 2);
                    v___x_1452_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_1437_, v_fst_1445_, v_snd_1446_, v_a_1430_, v_snd_1441_);
                    return v___x_1452_;
                } else {
                    crate::leanh::lean_dec(v_fst_1445_);
                    crate::leanh::lean_dec(v_fst_1437_);
                    if v_isShared_1449_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1448_, 0, v_e_1427_);
                        v___x_1454_ = v___x_1448_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_e_1427_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_snd_1446_);
                        v___x_1454_ = v_reuseFailAlloc_1458_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1454_);
                    v___x_1456_ = v___x_1443_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_snd_1441_);
                    v___x_1456_ = v_reuseFailAlloc_1457_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1456_;
            }
            6 => {
                v_fst_1480_ = crate::leanh::lean_ctor_get(v_fst_1475_, 0);
                v_snd_1481_ = crate::leanh::lean_ctor_get(v_fst_1475_, 1);
                v_isSharedCheck_1496_ = (!crate::leanh::lean_is_exclusive(v_fst_1475_)) as u8;
                if v_isSharedCheck_1496_ == 0 {
                    v___x_1483_ = v_fst_1475_;
                    v_isShared_1484_ = v_isSharedCheck_1496_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1481_);
                    crate::leanh::lean_inc(v_fst_1480_);
                    crate::leanh::lean_dec(v_fst_1475_);
                    v___x_1483_ = crate::leanh::lean_box(0);
                    v_isShared_1484_ = v_isSharedCheck_1496_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1494_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_1464_,
                        v_fst_1470_,
                    );
                if v___x_1494_ == 0 {
                    v___y_1486_ = v___x_1494_;
                    state = 8;
                    continue;
                } else {
                    v___x_1495_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1465_,
                            v_fst_1480_,
                        );
                    v___y_1486_ = v___x_1495_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_1486_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1463_);
                    crate::leanh::lean_del_object(v___x_1483_);
                    crate::leanh::lean_del_object(v___x_1478_);
                    crate::leanh::lean_dec_ref_known(v_e_1427_, 3);
                    v___x_1487_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_1463_, v_binderInfo_1466_, v_fst_1470_, v_fst_1480_, v_snd_1481_, v_a_1430_, v_snd_1476_);
                    return v___x_1487_;
                } else {
                    crate::leanh::lean_dec(v_fst_1480_);
                    crate::leanh::lean_dec(v_fst_1470_);
                    if v_isShared_1484_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1483_, 0, v_e_1427_);
                        v___x_1489_ = v___x_1483_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_e_1427_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_snd_1481_);
                        v___x_1489_ = v_reuseFailAlloc_1493_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1489_);
                    v___x_1491_ = v___x_1478_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1476_);
                    v___x_1491_ = v_reuseFailAlloc_1492_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1491_;
            }
            11 => {
                v_fst_1515_ = crate::leanh::lean_ctor_get(v_fst_1510_, 0);
                v_snd_1516_ = crate::leanh::lean_ctor_get(v_fst_1510_, 1);
                v_isSharedCheck_1531_ = (!crate::leanh::lean_is_exclusive(v_fst_1510_)) as u8;
                if v_isSharedCheck_1531_ == 0 {
                    v___x_1518_ = v_fst_1510_;
                    v_isShared_1519_ = v_isSharedCheck_1531_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1516_);
                    crate::leanh::lean_inc(v_fst_1515_);
                    crate::leanh::lean_dec(v_fst_1510_);
                    v___x_1518_ = crate::leanh::lean_box(0);
                    v_isShared_1519_ = v_isSharedCheck_1531_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1529_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_1499_,
                        v_fst_1505_,
                    );
                if v___x_1529_ == 0 {
                    v___y_1521_ = v___x_1529_;
                    state = 13;
                    continue;
                } else {
                    v___x_1530_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1500_,
                            v_fst_1515_,
                        );
                    v___y_1521_ = v___x_1530_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_1521_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1498_);
                    crate::leanh::lean_del_object(v___x_1518_);
                    crate::leanh::lean_del_object(v___x_1513_);
                    crate::leanh::lean_dec_ref_known(v_e_1427_, 3);
                    v___x_1522_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1498_, v_binderInfo_1501_, v_fst_1505_, v_fst_1515_, v_snd_1516_, v_a_1430_, v_snd_1511_);
                    return v___x_1522_;
                } else {
                    crate::leanh::lean_dec(v_fst_1515_);
                    crate::leanh::lean_dec(v_fst_1505_);
                    if v_isShared_1519_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1518_, 0, v_e_1427_);
                        v___x_1524_ = v___x_1518_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_e_1427_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_snd_1516_);
                        v___x_1524_ = v_reuseFailAlloc_1528_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1514_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1524_);
                    v___x_1526_ = v___x_1513_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_snd_1511_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1526_;
            }
            16 => {
                v_fst_1556_ = crate::leanh::lean_ctor_get(v_fst_1551_, 0);
                v_snd_1557_ = crate::leanh::lean_ctor_get(v_fst_1551_, 1);
                v_isSharedCheck_1574_ = (!crate::leanh::lean_is_exclusive(v_fst_1551_)) as u8;
                if v_isSharedCheck_1574_ == 0 {
                    v___x_1559_ = v_fst_1551_;
                    v_isShared_1560_ = v_isSharedCheck_1574_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1557_);
                    crate::leanh::lean_inc(v_fst_1556_);
                    crate::leanh::lean_dec(v_fst_1551_);
                    v___x_1559_ = crate::leanh::lean_box(0);
                    v_isShared_1560_ = v_isSharedCheck_1574_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1572_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_1534_,
                        v_fst_1541_,
                    );
                if v___x_1572_ == 0 {
                    v___y_1562_ = v___x_1572_;
                    state = 18;
                    continue;
                } else {
                    v___x_1573_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_1535_,
                            v_fst_1546_,
                        );
                    v___y_1562_ = v___x_1573_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_1562_ == 0 {
                    crate::leanh::lean_inc(v_declName_1533_);
                    crate::leanh::lean_del_object(v___x_1559_);
                    crate::leanh::lean_del_object(v___x_1554_);
                    crate::leanh::lean_dec_ref_known(v_e_1427_, 4);
                    v___x_1563_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1533_, v_fst_1541_, v_fst_1546_, v_fst_1556_, v_nondep_1537_, v_snd_1557_, v_a_1430_, v_snd_1552_);
                    return v___x_1563_;
                } else {
                    v___x_1564_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1536_,
                            v_fst_1556_,
                        );
                    if v___x_1564_ == 0 {
                        crate::leanh::lean_inc(v_declName_1533_);
                        crate::leanh::lean_del_object(v___x_1559_);
                        crate::leanh::lean_del_object(v___x_1554_);
                        crate::leanh::lean_dec_ref_known(v_e_1427_, 4);
                        v___x_1565_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1533_, v_fst_1541_, v_fst_1546_, v_fst_1556_, v_nondep_1537_, v_snd_1557_, v_a_1430_, v_snd_1552_);
                        return v___x_1565_;
                    } else {
                        crate::leanh::lean_dec(v_fst_1556_);
                        crate::leanh::lean_dec(v_fst_1546_);
                        crate::leanh::lean_dec(v_fst_1541_);
                        if v_isShared_1560_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1559_, 0, v_e_1427_);
                            v___x_1567_ = v___x_1559_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1571_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_e_1427_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_snd_1557_);
                            v___x_1567_ = v_reuseFailAlloc_1571_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1554_, 0, v___x_1567_);
                    v___x_1569_ = v___x_1554_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1552_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1569_;
            }
            21 => {
                v_fst_1584_ = crate::leanh::lean_ctor_get(v_fst_1579_, 0);
                v_snd_1585_ = crate::leanh::lean_ctor_get(v_fst_1579_, 1);
                v_isSharedCheck_1597_ = (!crate::leanh::lean_is_exclusive(v_fst_1579_)) as u8;
                if v_isSharedCheck_1597_ == 0 {
                    v___x_1587_ = v_fst_1579_;
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1585_);
                    crate::leanh::lean_inc(v_fst_1584_);
                    crate::leanh::lean_dec(v_fst_1579_);
                    v___x_1587_ = crate::leanh::lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1589_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_1577_,
                        v_fst_1584_,
                    );
                if v___x_1589_ == 0 {
                    crate::leanh::lean_inc(v_data_1576_);
                    crate::leanh::lean_del_object(v___x_1587_);
                    crate::leanh::lean_del_object(v___x_1582_);
                    crate::leanh::lean_dec_ref_known(v_e_1427_, 2);
                    v___x_1590_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1576_, v_fst_1584_, v_snd_1585_, v_a_1430_, v_snd_1580_);
                    return v___x_1590_;
                } else {
                    crate::leanh::lean_dec(v_fst_1584_);
                    if v_isShared_1588_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1587_, 0, v_e_1427_);
                        v___x_1592_ = v___x_1587_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_e_1427_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_snd_1585_);
                        v___x_1592_ = v_reuseFailAlloc_1596_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1592_);
                    v___x_1594_ = v___x_1582_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_snd_1580_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1594_;
            }
            25 => {
                v_fst_1608_ = crate::leanh::lean_ctor_get(v_fst_1603_, 0);
                v_snd_1609_ = crate::leanh::lean_ctor_get(v_fst_1603_, 1);
                v_isSharedCheck_1621_ = (!crate::leanh::lean_is_exclusive(v_fst_1603_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v___x_1611_ = v_fst_1603_;
                    v_isShared_1612_ = v_isSharedCheck_1621_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1609_);
                    crate::leanh::lean_inc(v_fst_1608_);
                    crate::leanh::lean_dec(v_fst_1603_);
                    v___x_1611_ = crate::leanh::lean_box(0);
                    v_isShared_1612_ = v_isSharedCheck_1621_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_1613_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_1601_,
                        v_fst_1608_,
                    );
                if v___x_1613_ == 0 {
                    crate::leanh::lean_inc(v_idx_1600_);
                    crate::leanh::lean_inc(v_typeName_1599_);
                    crate::leanh::lean_del_object(v___x_1611_);
                    crate::leanh::lean_del_object(v___x_1606_);
                    crate::leanh::lean_dec_ref_known(v_e_1427_, 3);
                    v___x_1614_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1599_, v_idx_1600_, v_fst_1608_, v_snd_1609_, v_a_1430_, v_snd_1604_);
                    return v___x_1614_;
                } else {
                    crate::leanh::lean_dec(v_fst_1608_);
                    if v_isShared_1612_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1611_, 0, v_e_1427_);
                        v___x_1616_ = v___x_1611_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_e_1427_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_snd_1609_);
                        v___x_1616_ = v_reuseFailAlloc_1620_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_1607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1616_);
                    v___x_1618_ = v___x_1606_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_snd_1604_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(
    mut v_s_1625_: *mut crate::leanh::LeanObject,
    mut v_d_1626_: *mut crate::leanh::LeanObject,
    mut v_e_1627_: *mut crate::leanh::LeanObject,
    mut v_offset_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: u8,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_u2081_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    let mut v_deBruijnIndex_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_offset_1628_);
                crate::leanh::lean_inc_ref(v_e_1627_);
                v_key_1632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_key_1632_, 0, v_e_1627_);
                crate::leanh::lean_ctor_set(v_key_1632_, 1, v_offset_1628_);
                v___x_1647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1629_, v_key_1632_);
                if crate::leanh::lean_obj_tag(v___x_1647_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_key_1632_, 2);
                    crate::leanh::lean_dec(v_offset_1628_);
                    crate::leanh::lean_dec_ref(v_e_1627_);
                    v_val_1648_ = crate::leanh::lean_ctor_get(v___x_1647_, 0);
                    crate::leanh::lean_inc(v_val_1648_);
                    crate::leanh::lean_dec_ref_known(v___x_1647_, 1);
                    v___x_1649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1649_, 0, v_val_1648_);
                    crate::leanh::lean_ctor_set(v___x_1649_, 1, v_a_1629_);
                    v___x_1650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1650_, 0, v___x_1649_);
                    crate::leanh::lean_ctor_set(v___x_1650_, 1, v_a_1631_);
                    return v___x_1650_;
                } else {
                    crate::leanh::lean_dec(v___x_1647_);
                    v_s_u2081_1651_ = lean_nat_add(v_s_1625_, v_offset_1628_);
                    v___x_1652_ = l_Lean_Expr_looseBVarRange(v_e_1627_);
                    v___x_1653_ = lean_nat_dec_le(v___x_1652_, v_s_u2081_1651_);
                    crate::leanh::lean_dec(v___x_1652_);
                    if v___x_1653_ == 0 {
                        if crate::leanh::lean_obj_tag(v_e_1627_) == 0 {
                            v_deBruijnIndex_1654_ = crate::leanh::lean_ctor_get(v_e_1627_, 0);
                            v___x_1655_ = lean_nat_dec_le(v_s_u2081_1651_, v_deBruijnIndex_1654_);
                            crate::leanh::lean_dec(v_s_u2081_1651_);
                            if v___x_1655_ == 0 {
                                v_snd_1634_ = v_a_1631_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_deBruijnIndex_1654_);
                                crate::leanh::lean_dec_ref_known(v_e_1627_, 1);
                                crate::leanh::lean_dec(v_offset_1628_);
                                v___x_1656_ = lean_nat_sub(v_deBruijnIndex_1654_, v_d_1626_);
                                crate::leanh::lean_dec(v_deBruijnIndex_1654_);
                                v___x_1657_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1656_, v_a_1631_);
                                v_fst_1658_ = crate::leanh::lean_ctor_get(v___x_1657_, 0);
                                crate::leanh::lean_inc(v_fst_1658_);
                                v_snd_1659_ = crate::leanh::lean_ctor_get(v___x_1657_, 1);
                                crate::leanh::lean_inc(v_snd_1659_);
                                crate::leanh::lean_dec_ref(v___x_1657_);
                                v___x_1660_ =
                                    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                        v_key_1632_,
                                        v_fst_1658_,
                                        v_a_1629_,
                                        v_a_1630_,
                                        v_snd_1659_,
                                    );
                                return v___x_1660_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_s_u2081_1651_);
                            v_snd_1634_ = v_a_1631_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_s_u2081_1651_);
                        crate::leanh::lean_dec(v_offset_1628_);
                        v___x_1661_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_1632_,
                            v_e_1627_,
                            v_a_1629_,
                            v_a_1630_,
                            v_a_1631_,
                        );
                        return v___x_1661_;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_e_1627_) {
                9 => {
                    crate::leanh::lean_dec(v_offset_1628_);
                    v___x_1635_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_e_1627_,
                        v_a_1629_,
                        v_a_1630_,
                        v_snd_1634_,
                    );
                    return v___x_1635_;
                }
                2 => {
                    crate::leanh::lean_dec(v_offset_1628_);
                    v___x_1636_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_e_1627_,
                        v_a_1629_,
                        v_a_1630_,
                        v_snd_1634_,
                    );
                    return v___x_1636_;
                }
                0 => {
                    crate::leanh::lean_dec(v_offset_1628_);
                    v___x_1637_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_e_1627_,
                        v_a_1629_,
                        v_a_1630_,
                        v_snd_1634_,
                    );
                    return v___x_1637_;
                }
                1 => {
                    crate::leanh::lean_dec(v_offset_1628_);
                    v___x_1638_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_e_1627_,
                        v_a_1629_,
                        v_a_1630_,
                        v_snd_1634_,
                    );
                    return v___x_1638_;
                }
                4 => {
                    crate::leanh::lean_dec(v_offset_1628_);
                    v___x_1639_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_e_1627_,
                        v_a_1629_,
                        v_a_1630_,
                        v_snd_1634_,
                    );
                    return v___x_1639_;
                }
                3 => {
                    crate::leanh::lean_dec(v_offset_1628_);
                    v___x_1640_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_e_1627_,
                        v_a_1629_,
                        v_a_1630_,
                        v_snd_1634_,
                    );
                    return v___x_1640_;
                }
                _ => {
                    v___x_1641_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_1625_, v_d_1626_, v_e_1627_, v_offset_1628_, v_a_1629_, v_a_1630_, v_snd_1634_);
                    v_fst_1642_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                    crate::leanh::lean_inc(v_fst_1642_);
                    v_snd_1643_ = crate::leanh::lean_ctor_get(v___x_1641_, 1);
                    crate::leanh::lean_inc(v_snd_1643_);
                    crate::leanh::lean_dec_ref(v___x_1641_);
                    v_fst_1644_ = crate::leanh::lean_ctor_get(v_fst_1642_, 0);
                    crate::leanh::lean_inc(v_fst_1644_);
                    v_snd_1645_ = crate::leanh::lean_ctor_get(v_fst_1642_, 1);
                    crate::leanh::lean_inc(v_snd_1645_);
                    crate::leanh::lean_dec(v_fst_1642_);
                    v___x_1646_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_1632_,
                        v_fst_1644_,
                        v_snd_1645_,
                        v_a_1630_,
                        v_snd_1643_,
                    );
                    return v___x_1646_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(
    mut v_s_1662_: *mut crate::leanh::LeanObject,
    mut v_d_1663_: *mut crate::leanh::LeanObject,
    mut v_e_1664_: *mut crate::leanh::LeanObject,
    mut v_offset_1665_: *mut crate::leanh::LeanObject,
    mut v_a_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
    mut v_a_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1669_: u8 = 0;
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1669_ = (crate::leanh::lean_unbox(v_a_1667_) as u8);
    v_res_1670_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1662_, v_d_1663_, v_e_1664_, v_offset_1665_, v_a_1666_, v_a_boxed_1669_, v_a_1668_);
    crate::leanh::lean_dec(v_d_1663_);
    crate::leanh::lean_dec(v_s_1662_);
    return v_res_1670_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(
    mut v_s_1671_: *mut crate::leanh::LeanObject,
    mut v_d_1672_: *mut crate::leanh::LeanObject,
    mut v_e_1673_: *mut crate::leanh::LeanObject,
    mut v_offset_1674_: *mut crate::leanh::LeanObject,
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1678_: u8 = 0;
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1678_ = (crate::leanh::lean_unbox(v_a_1676_) as u8);
    v_res_1679_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_1671_, v_d_1672_, v_e_1673_, v_offset_1674_, v_a_1675_, v_a_boxed_1678_, v_a_1677_);
    crate::leanh::lean_dec(v_d_1672_);
    crate::leanh::lean_dec(v_s_1671_);
    return v_res_1679_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = crate::leanh::lean_box(0);
    v___x_1681_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1682_ = lean_mk_array(v___x_1681_, v___x_1680_);
    return v___x_1682_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once),
        _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0,
    );
    v___x_1684_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1685_, 0, v___x_1684_);
    crate::leanh::lean_ctor_set(v___x_1685_, 1, v___x_1683_);
    return v___x_1685_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS_x27(
    mut v_e_1686_: *mut crate::leanh::LeanObject,
    mut v_s_1687_: *mut crate::leanh::LeanObject,
    mut v_d_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: u8,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_unused_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1691_ = l_Lean_Expr_looseBVarRange(v_e_1686_);
                v___x_1692_ = lean_nat_dec_le(v___x_1691_, v_s_1687_);
                crate::leanh::lean_dec(v___x_1691_);
                if v___x_1692_ == 0 {
                    v___x_1693_ = crate::leanh::lean_unsigned_to_nat(0);
                    if crate::leanh::lean_obj_tag(v_e_1686_) == 0 {
                        v_deBruijnIndex_1715_ = crate::leanh::lean_ctor_get(v_e_1686_, 0);
                        v___x_1716_ = lean_nat_dec_le(v_s_1687_, v_deBruijnIndex_1715_);
                        if v___x_1716_ == 0 {
                            v_snd_1695_ = v_a_1690_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_deBruijnIndex_1715_);
                            crate::leanh::lean_dec_ref_known(v_e_1686_, 1);
                            v___x_1717_ = lean_nat_sub(v_deBruijnIndex_1715_, v_d_1688_);
                            crate::leanh::lean_dec(v_deBruijnIndex_1715_);
                            v___x_1718_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1717_, v_a_1690_);
                            return v___x_1718_;
                        }
                    } else {
                        v_snd_1695_ = v_a_1690_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1719_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1719_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1719_, 1, v_a_1690_);
                    return v___x_1719_;
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_e_1686_) {
                9 => {
                    v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1696_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1696_, 1, v_snd_1695_);
                    return v___x_1696_;
                }
                2 => {
                    v___x_1697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1697_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1697_, 1, v_snd_1695_);
                    return v___x_1697_;
                }
                0 => {
                    v___x_1698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1698_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1698_, 1, v_snd_1695_);
                    return v___x_1698_;
                }
                1 => {
                    v___x_1699_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1699_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1699_, 1, v_snd_1695_);
                    return v___x_1699_;
                }
                4 => {
                    v___x_1700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1700_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1700_, 1, v_snd_1695_);
                    return v___x_1700_;
                }
                3 => {
                    v___x_1701_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1701_, 0, v_e_1686_);
                    crate::leanh::lean_ctor_set(v___x_1701_, 1, v_snd_1695_);
                    return v___x_1701_;
                }
                _ => {
                    v___x_1702_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1,
                    );
                    v___x_1703_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_1687_, v_d_1688_, v_e_1686_, v___x_1693_, v___x_1702_, v_a_1689_, v_snd_1695_);
                    v_fst_1704_ = crate::leanh::lean_ctor_get(v___x_1703_, 0);
                    crate::leanh::lean_inc(v_fst_1704_);
                    v_snd_1705_ = crate::leanh::lean_ctor_get(v___x_1703_, 1);
                    crate::leanh::lean_inc(v_snd_1705_);
                    crate::leanh::lean_dec_ref(v___x_1703_);
                    v_fst_1706_ = crate::leanh::lean_ctor_get(v_fst_1704_, 0);
                    v_isSharedCheck_1713_ = (!crate::leanh::lean_is_exclusive(v_fst_1704_)) as u8;
                    if v_isSharedCheck_1713_ == 0 {
                        v_unused_1714_ = crate::leanh::lean_ctor_get(v_fst_1704_, 1);
                        crate::leanh::lean_dec(v_unused_1714_);
                        v___x_1708_ = v_fst_1704_;
                        v_isShared_1709_ = v_isSharedCheck_1713_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1706_);
                        crate::leanh::lean_dec(v_fst_1704_);
                        v___x_1708_ = crate::leanh::lean_box(0);
                        v_isShared_1709_ = v_isSharedCheck_1713_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => {
                if v_isShared_1709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1708_, 1, v_snd_1705_);
                    v___x_1711_ = v___x_1708_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_fst_1706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_snd_1705_);
                    v___x_1711_ = v_reuseFailAlloc_1712_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(
    mut v_e_1720_: *mut crate::leanh::LeanObject,
    mut v_s_1721_: *mut crate::leanh::LeanObject,
    mut v_d_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1725_: u8 = 0;
    let mut v_res_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1725_ = (crate::leanh::lean_unbox(v_a_1723_) as u8);
    v_res_1726_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(
        v_e_1720_,
        v_s_1721_,
        v_d_1722_,
        v_a_boxed_1725_,
        v_a_1724_,
    );
    crate::leanh::lean_dec(v_d_1722_);
    crate::leanh::lean_dec(v_s_1721_);
    return v_res_1726_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1727_: *mut crate::leanh::LeanObject,
    mut v_m_1728_: *mut crate::leanh::LeanObject,
    mut v_a_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_1728_, v_a_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_1731_: *mut crate::leanh::LeanObject,
    mut v_m_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_1731_, v_m_1732_, v_a_1733_);
    crate::leanh::lean_dec_ref(v_a_1733_);
    crate::leanh::lean_dec_ref(v_m_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(
    mut v_00_u03b2_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
    mut v_x_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_1736_, v_x_1737_);
    return v___x_1738_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(
    mut v_00_u03b2_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_x_1741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1742_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_1739_, v_a_1740_, v_x_1741_);
    crate::leanh::lean_dec(v_x_1741_);
    crate::leanh::lean_dec_ref(v_a_1740_);
    return v_res_1742_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1743_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
    v___x_1745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(
    mut v_00_u03b2_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1);
    return v___x_1747_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(
        crate::leanh::lean_box(0),
    );
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(
    mut v_e_1749_: *mut crate::leanh::LeanObject,
    mut v_s_1750_: *mut crate::leanh::LeanObject,
    mut v_d_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1765_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1774_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1788_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut v_unused_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1754_ = lean_st_ref_take(v_a_1752_);
                v_share_1755_ = crate::leanh::lean_ctor_get(v___x_1754_, 0);
                v_maxFVar_1756_ = crate::leanh::lean_ctor_get(v___x_1754_, 1);
                v_proofInstInfo_1757_ = crate::leanh::lean_ctor_get(v___x_1754_, 2);
                v_inferType_1758_ = crate::leanh::lean_ctor_get(v___x_1754_, 3);
                v_getLevel_1759_ = crate::leanh::lean_ctor_get(v___x_1754_, 4);
                v_congrInfo_1760_ = crate::leanh::lean_ctor_get(v___x_1754_, 5);
                v_defEqI_1761_ = crate::leanh::lean_ctor_get(v___x_1754_, 6);
                v_extensions_1762_ = crate::leanh::lean_ctor_get(v___x_1754_, 7);
                v_issues_1763_ = crate::leanh::lean_ctor_get(v___x_1754_, 8);
                v_canon_1764_ = crate::leanh::lean_ctor_get(v___x_1754_, 9);
                v_debug_1765_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1754_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1800_ = (!crate::leanh::lean_is_exclusive(v___x_1754_)) as u8;
                if v_isSharedCheck_1800_ == 0 {
                    v___x_1767_ = v___x_1754_;
                    v_isShared_1768_ = v_isSharedCheck_1800_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1764_);
                    crate::leanh::lean_inc(v_issues_1763_);
                    crate::leanh::lean_inc(v_extensions_1762_);
                    crate::leanh::lean_inc(v_defEqI_1761_);
                    crate::leanh::lean_inc(v_congrInfo_1760_);
                    crate::leanh::lean_inc(v_getLevel_1759_);
                    crate::leanh::lean_inc(v_inferType_1758_);
                    crate::leanh::lean_inc(v_proofInstInfo_1757_);
                    crate::leanh::lean_inc(v_maxFVar_1756_);
                    crate::leanh::lean_inc(v_share_1755_);
                    crate::leanh::lean_dec(v___x_1754_);
                    v___x_1767_ = crate::leanh::lean_box(0);
                    v_isShared_1768_ = v_isSharedCheck_1800_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1769_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0,
                );
                if v_isShared_1768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1767_, 0, v___x_1769_);
                    v___x_1771_ = v___x_1767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_maxFVar_1756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_proofInstInfo_1757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_inferType_1758_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_getLevel_1759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_congrInfo_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_defEqI_1761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_extensions_1762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_issues_1763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 9, v_canon_1764_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1799_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1765_,
                    );
                    v___x_1771_ = v_reuseFailAlloc_1799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1772_ = lean_st_ref_set(v_a_1752_, v___x_1771_);
                v___x_1773_ = lean_st_ref_get(v_a_1752_);
                v_debug_1774_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_1773_);
                v___x_1775_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(
                    v_e_1749_,
                    v_s_1750_,
                    v_d_1751_,
                    v_debug_1774_,
                    v_share_1755_,
                );
                v_fst_1776_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                crate::leanh::lean_inc(v_fst_1776_);
                v_snd_1777_ = crate::leanh::lean_ctor_get(v___x_1775_, 1);
                crate::leanh::lean_inc(v_snd_1777_);
                crate::leanh::lean_dec_ref(v___x_1775_);
                v___x_1778_ = lean_st_ref_take(v_a_1752_);
                v_maxFVar_1779_ = crate::leanh::lean_ctor_get(v___x_1778_, 1);
                v_proofInstInfo_1780_ = crate::leanh::lean_ctor_get(v___x_1778_, 2);
                v_inferType_1781_ = crate::leanh::lean_ctor_get(v___x_1778_, 3);
                v_getLevel_1782_ = crate::leanh::lean_ctor_get(v___x_1778_, 4);
                v_congrInfo_1783_ = crate::leanh::lean_ctor_get(v___x_1778_, 5);
                v_defEqI_1784_ = crate::leanh::lean_ctor_get(v___x_1778_, 6);
                v_extensions_1785_ = crate::leanh::lean_ctor_get(v___x_1778_, 7);
                v_issues_1786_ = crate::leanh::lean_ctor_get(v___x_1778_, 8);
                v_canon_1787_ = crate::leanh::lean_ctor_get(v___x_1778_, 9);
                v_debug_1788_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1797_ = (!crate::leanh::lean_is_exclusive(v___x_1778_)) as u8;
                if v_isSharedCheck_1797_ == 0 {
                    v_unused_1798_ = crate::leanh::lean_ctor_get(v___x_1778_, 0);
                    crate::leanh::lean_dec(v_unused_1798_);
                    v___x_1790_ = v___x_1778_;
                    v_isShared_1791_ = v_isSharedCheck_1797_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1787_);
                    crate::leanh::lean_inc(v_issues_1786_);
                    crate::leanh::lean_inc(v_extensions_1785_);
                    crate::leanh::lean_inc(v_defEqI_1784_);
                    crate::leanh::lean_inc(v_congrInfo_1783_);
                    crate::leanh::lean_inc(v_getLevel_1782_);
                    crate::leanh::lean_inc(v_inferType_1781_);
                    crate::leanh::lean_inc(v_proofInstInfo_1780_);
                    crate::leanh::lean_inc(v_maxFVar_1779_);
                    crate::leanh::lean_dec(v___x_1778_);
                    v___x_1790_ = crate::leanh::lean_box(0);
                    v_isShared_1791_ = v_isSharedCheck_1797_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1790_, 0, v_snd_1777_);
                    v___x_1793_ = v___x_1790_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_snd_1777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_maxFVar_1779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_proofInstInfo_1780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_inferType_1781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_getLevel_1782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_congrInfo_1783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 6, v_defEqI_1784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 7, v_extensions_1785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 8, v_issues_1786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 9, v_canon_1787_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1796_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1788_,
                    );
                    v___x_1793_ = v_reuseFailAlloc_1796_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1794_ = lean_st_ref_set(v_a_1752_, v___x_1793_);
                v___x_1795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1795_, 0, v_fst_1776_);
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___boxed(
    mut v_e_1801_: *mut crate::leanh::LeanObject,
    mut v_s_1802_: *mut crate::leanh::LeanObject,
    mut v_d_1803_: *mut crate::leanh::LeanObject,
    mut v_a_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ =
        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_1801_, v_s_1802_, v_d_1803_, v_a_1804_);
    crate::leanh::lean_dec(v_a_1804_);
    crate::leanh::lean_dec(v_d_1803_);
    crate::leanh::lean_dec(v_s_1802_);
    return v_res_1806_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS(
    mut v_e_1807_: *mut crate::leanh::LeanObject,
    mut v_s_1808_: *mut crate::leanh::LeanObject,
    mut v_d_1809_: *mut crate::leanh::LeanObject,
    mut v_a_1810_: *mut crate::leanh::LeanObject,
    mut v_a_1811_: *mut crate::leanh::LeanObject,
    mut v_a_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ =
        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_1807_, v_s_1808_, v_d_1809_, v_a_1811_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(
    mut v_e_1818_: *mut crate::leanh::LeanObject,
    mut v_s_1819_: *mut crate::leanh::LeanObject,
    mut v_d_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lean_Meta_Sym_lowerLooseBVarsS(
        v_e_1818_, v_s_1819_, v_d_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_,
        v_a_1826_,
    );
    crate::leanh::lean_dec(v_a_1826_);
    crate::leanh::lean_dec_ref(v_a_1825_);
    crate::leanh::lean_dec(v_a_1824_);
    crate::leanh::lean_dec_ref(v_a_1823_);
    crate::leanh::lean_dec(v_a_1822_);
    crate::leanh::lean_dec_ref(v_a_1821_);
    crate::leanh::lean_dec(v_d_1820_);
    crate::leanh::lean_dec(v_s_1819_);
    return v_res_1828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(
    mut v_s_1829_: *mut crate::leanh::LeanObject,
    mut v_d_1830_: *mut crate::leanh::LeanObject,
    mut v_e_1831_: *mut crate::leanh::LeanObject,
    mut v_offset_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: u8,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v_fst_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___y_1855_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_binderName_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1870_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v_fst_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___y_1890_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u8 = 0;
    let mut v___x_1899_: u8 = 0;
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut v_binderName_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1905_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1918_: u8 = 0;
    let mut v_fst_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___y_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: u8 = 0;
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_declName_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1941_: u8 = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v_fst_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___y_1966_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: u8 = 0;
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_data_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v_fst_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_typeName_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v_fst_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_1831_) {
                5 => {
                    v_fn_1836_ = crate::leanh::lean_ctor_get(v_e_1831_, 0);
                    v_arg_1837_ = crate::leanh::lean_ctor_get(v_e_1831_, 1);
                    crate::leanh::lean_inc(v_offset_1832_);
                    crate::leanh::lean_inc_ref(v_fn_1836_);
                    v___x_1838_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_fn_1836_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1839_ = crate::leanh::lean_ctor_get(v___x_1838_, 0);
                    crate::leanh::lean_inc(v_fst_1839_);
                    v_snd_1840_ = crate::leanh::lean_ctor_get(v___x_1838_, 1);
                    crate::leanh::lean_inc(v_snd_1840_);
                    crate::leanh::lean_dec_ref(v___x_1838_);
                    v_fst_1841_ = crate::leanh::lean_ctor_get(v_fst_1839_, 0);
                    crate::leanh::lean_inc(v_fst_1841_);
                    v_snd_1842_ = crate::leanh::lean_ctor_get(v_fst_1839_, 1);
                    crate::leanh::lean_inc(v_snd_1842_);
                    crate::leanh::lean_dec(v_fst_1839_);
                    crate::leanh::lean_inc_ref(v_arg_1837_);
                    v___x_1843_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_arg_1837_, v_offset_1832_, v_snd_1842_, v_a_1834_, v_snd_1840_);
                    v_fst_1844_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
                    v_snd_1845_ = crate::leanh::lean_ctor_get(v___x_1843_, 1);
                    v_isSharedCheck_1866_ = (!crate::leanh::lean_is_exclusive(v___x_1843_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v___x_1847_ = v___x_1843_;
                        v_isShared_1848_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1845_);
                        crate::leanh::lean_inc(v_fst_1844_);
                        crate::leanh::lean_dec(v___x_1843_);
                        v___x_1847_ = crate::leanh::lean_box(0);
                        v_isShared_1848_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_1867_ = crate::leanh::lean_ctor_get(v_e_1831_, 0);
                    v_binderType_1868_ = crate::leanh::lean_ctor_get(v_e_1831_, 1);
                    v_body_1869_ = crate::leanh::lean_ctor_get(v_e_1831_, 2);
                    v_binderInfo_1870_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1831_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_1832_);
                    crate::leanh::lean_inc_ref(v_binderType_1868_);
                    v___x_1871_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_binderType_1868_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1872_ = crate::leanh::lean_ctor_get(v___x_1871_, 0);
                    crate::leanh::lean_inc(v_fst_1872_);
                    v_snd_1873_ = crate::leanh::lean_ctor_get(v___x_1871_, 1);
                    crate::leanh::lean_inc(v_snd_1873_);
                    crate::leanh::lean_dec_ref(v___x_1871_);
                    v_fst_1874_ = crate::leanh::lean_ctor_get(v_fst_1872_, 0);
                    crate::leanh::lean_inc(v_fst_1874_);
                    v_snd_1875_ = crate::leanh::lean_ctor_get(v_fst_1872_, 1);
                    crate::leanh::lean_inc(v_snd_1875_);
                    crate::leanh::lean_dec(v_fst_1872_);
                    v___x_1876_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1877_ = lean_nat_add(v_offset_1832_, v___x_1876_);
                    crate::leanh::lean_dec(v_offset_1832_);
                    crate::leanh::lean_inc_ref(v_body_1869_);
                    v___x_1878_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_body_1869_, v___x_1877_, v_snd_1875_, v_a_1834_, v_snd_1873_);
                    v_fst_1879_ = crate::leanh::lean_ctor_get(v___x_1878_, 0);
                    v_snd_1880_ = crate::leanh::lean_ctor_get(v___x_1878_, 1);
                    v_isSharedCheck_1901_ = (!crate::leanh::lean_is_exclusive(v___x_1878_)) as u8;
                    if v_isSharedCheck_1901_ == 0 {
                        v___x_1882_ = v___x_1878_;
                        v_isShared_1883_ = v_isSharedCheck_1901_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1880_);
                        crate::leanh::lean_inc(v_fst_1879_);
                        crate::leanh::lean_dec(v___x_1878_);
                        v___x_1882_ = crate::leanh::lean_box(0);
                        v_isShared_1883_ = v_isSharedCheck_1901_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_1902_ = crate::leanh::lean_ctor_get(v_e_1831_, 0);
                    v_binderType_1903_ = crate::leanh::lean_ctor_get(v_e_1831_, 1);
                    v_body_1904_ = crate::leanh::lean_ctor_get(v_e_1831_, 2);
                    v_binderInfo_1905_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1831_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_1832_);
                    crate::leanh::lean_inc_ref(v_binderType_1903_);
                    v___x_1906_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_binderType_1903_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1907_ = crate::leanh::lean_ctor_get(v___x_1906_, 0);
                    crate::leanh::lean_inc(v_fst_1907_);
                    v_snd_1908_ = crate::leanh::lean_ctor_get(v___x_1906_, 1);
                    crate::leanh::lean_inc(v_snd_1908_);
                    crate::leanh::lean_dec_ref(v___x_1906_);
                    v_fst_1909_ = crate::leanh::lean_ctor_get(v_fst_1907_, 0);
                    crate::leanh::lean_inc(v_fst_1909_);
                    v_snd_1910_ = crate::leanh::lean_ctor_get(v_fst_1907_, 1);
                    crate::leanh::lean_inc(v_snd_1910_);
                    crate::leanh::lean_dec(v_fst_1907_);
                    v___x_1911_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1912_ = lean_nat_add(v_offset_1832_, v___x_1911_);
                    crate::leanh::lean_dec(v_offset_1832_);
                    crate::leanh::lean_inc_ref(v_body_1904_);
                    v___x_1913_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_body_1904_, v___x_1912_, v_snd_1910_, v_a_1834_, v_snd_1908_);
                    v_fst_1914_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                    v_snd_1915_ = crate::leanh::lean_ctor_get(v___x_1913_, 1);
                    v_isSharedCheck_1936_ = (!crate::leanh::lean_is_exclusive(v___x_1913_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v___x_1917_ = v___x_1913_;
                        v_isShared_1918_ = v_isSharedCheck_1936_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1915_);
                        crate::leanh::lean_inc(v_fst_1914_);
                        crate::leanh::lean_dec(v___x_1913_);
                        v___x_1917_ = crate::leanh::lean_box(0);
                        v_isShared_1918_ = v_isSharedCheck_1936_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_1937_ = crate::leanh::lean_ctor_get(v_e_1831_, 0);
                    v_type_1938_ = crate::leanh::lean_ctor_get(v_e_1831_, 1);
                    v_value_1939_ = crate::leanh::lean_ctor_get(v_e_1831_, 2);
                    v_body_1940_ = crate::leanh::lean_ctor_get(v_e_1831_, 3);
                    v_nondep_1941_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_1831_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_n(v_offset_1832_, 2);
                    crate::leanh::lean_inc_ref(v_type_1938_);
                    v___x_1942_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_type_1938_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1943_ = crate::leanh::lean_ctor_get(v___x_1942_, 0);
                    crate::leanh::lean_inc(v_fst_1943_);
                    v_snd_1944_ = crate::leanh::lean_ctor_get(v___x_1942_, 1);
                    crate::leanh::lean_inc(v_snd_1944_);
                    crate::leanh::lean_dec_ref(v___x_1942_);
                    v_fst_1945_ = crate::leanh::lean_ctor_get(v_fst_1943_, 0);
                    crate::leanh::lean_inc(v_fst_1945_);
                    v_snd_1946_ = crate::leanh::lean_ctor_get(v_fst_1943_, 1);
                    crate::leanh::lean_inc(v_snd_1946_);
                    crate::leanh::lean_dec(v_fst_1943_);
                    crate::leanh::lean_inc_ref(v_value_1939_);
                    v___x_1947_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_value_1939_, v_offset_1832_, v_snd_1946_, v_a_1834_, v_snd_1944_);
                    v_fst_1948_ = crate::leanh::lean_ctor_get(v___x_1947_, 0);
                    crate::leanh::lean_inc(v_fst_1948_);
                    v_snd_1949_ = crate::leanh::lean_ctor_get(v___x_1947_, 1);
                    crate::leanh::lean_inc(v_snd_1949_);
                    crate::leanh::lean_dec_ref(v___x_1947_);
                    v_fst_1950_ = crate::leanh::lean_ctor_get(v_fst_1948_, 0);
                    crate::leanh::lean_inc(v_fst_1950_);
                    v_snd_1951_ = crate::leanh::lean_ctor_get(v_fst_1948_, 1);
                    crate::leanh::lean_inc(v_snd_1951_);
                    crate::leanh::lean_dec(v_fst_1948_);
                    v___x_1952_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1953_ = lean_nat_add(v_offset_1832_, v___x_1952_);
                    crate::leanh::lean_dec(v_offset_1832_);
                    crate::leanh::lean_inc_ref(v_body_1940_);
                    v___x_1954_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_body_1940_, v___x_1953_, v_snd_1951_, v_a_1834_, v_snd_1949_);
                    v_fst_1955_ = crate::leanh::lean_ctor_get(v___x_1954_, 0);
                    v_snd_1956_ = crate::leanh::lean_ctor_get(v___x_1954_, 1);
                    v_isSharedCheck_1979_ = (!crate::leanh::lean_is_exclusive(v___x_1954_)) as u8;
                    if v_isSharedCheck_1979_ == 0 {
                        v___x_1958_ = v___x_1954_;
                        v_isShared_1959_ = v_isSharedCheck_1979_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1956_);
                        crate::leanh::lean_inc(v_fst_1955_);
                        crate::leanh::lean_dec(v___x_1954_);
                        v___x_1958_ = crate::leanh::lean_box(0);
                        v_isShared_1959_ = v_isSharedCheck_1979_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_1980_ = crate::leanh::lean_ctor_get(v_e_1831_, 0);
                    v_expr_1981_ = crate::leanh::lean_ctor_get(v_e_1831_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1981_);
                    v___x_1982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_expr_1981_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1983_ = crate::leanh::lean_ctor_get(v___x_1982_, 0);
                    v_snd_1984_ = crate::leanh::lean_ctor_get(v___x_1982_, 1);
                    v_isSharedCheck_2002_ = (!crate::leanh::lean_is_exclusive(v___x_1982_)) as u8;
                    if v_isSharedCheck_2002_ == 0 {
                        v___x_1986_ = v___x_1982_;
                        v_isShared_1987_ = v_isSharedCheck_2002_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1984_);
                        crate::leanh::lean_inc(v_fst_1983_);
                        crate::leanh::lean_dec(v___x_1982_);
                        v___x_1986_ = crate::leanh::lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_2002_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_2003_ = crate::leanh::lean_ctor_get(v_e_1831_, 0);
                    v_idx_2004_ = crate::leanh::lean_ctor_get(v_e_1831_, 1);
                    v_struct_2005_ = crate::leanh::lean_ctor_get(v_e_1831_, 2);
                    crate::leanh::lean_inc_ref(v_struct_2005_);
                    v___x_2006_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_struct_2005_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_2007_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                    v_snd_2008_ = crate::leanh::lean_ctor_get(v___x_2006_, 1);
                    v_isSharedCheck_2026_ = (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                    if v_isSharedCheck_2026_ == 0 {
                        v___x_2010_ = v___x_2006_;
                        v_isShared_2011_ = v_isSharedCheck_2026_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2008_);
                        crate::leanh::lean_inc(v_fst_2007_);
                        crate::leanh::lean_dec(v___x_2006_);
                        v___x_2010_ = crate::leanh::lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2026_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_offset_1832_);
                    crate::leanh::lean_dec_ref(v_e_1831_);
                    v___x_2027_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
                    v___x_2028_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_2027_, v_a_1833_, v_a_1834_, v_a_1835_);
                    return v___x_2028_;
                }
            },
            1 => {
                v_fst_1849_ = crate::leanh::lean_ctor_get(v_fst_1844_, 0);
                v_snd_1850_ = crate::leanh::lean_ctor_get(v_fst_1844_, 1);
                v_isSharedCheck_1865_ = (!crate::leanh::lean_is_exclusive(v_fst_1844_)) as u8;
                if v_isSharedCheck_1865_ == 0 {
                    v___x_1852_ = v_fst_1844_;
                    v_isShared_1853_ = v_isSharedCheck_1865_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1850_);
                    crate::leanh::lean_inc(v_fst_1849_);
                    crate::leanh::lean_dec(v_fst_1844_);
                    v___x_1852_ = crate::leanh::lean_box(0);
                    v_isShared_1853_ = v_isSharedCheck_1865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1863_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_1836_,
                        v_fst_1841_,
                    );
                if v___x_1863_ == 0 {
                    v___y_1855_ = v___x_1863_;
                    state = 3;
                    continue;
                } else {
                    v___x_1864_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_1837_,
                            v_fst_1849_,
                        );
                    v___y_1855_ = v___x_1864_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_1855_ == 0 {
                    crate::leanh::lean_del_object(v___x_1852_);
                    crate::leanh::lean_del_object(v___x_1847_);
                    crate::leanh::lean_dec_ref_known(v_e_1831_, 2);
                    v___x_1856_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_1841_, v_fst_1849_, v_snd_1850_, v_a_1834_, v_snd_1845_);
                    return v___x_1856_;
                } else {
                    crate::leanh::lean_dec(v_fst_1849_);
                    crate::leanh::lean_dec(v_fst_1841_);
                    if v_isShared_1853_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1852_, 0, v_e_1831_);
                        v___x_1858_ = v___x_1852_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_e_1831_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_snd_1850_);
                        v___x_1858_ = v_reuseFailAlloc_1862_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1847_, 0, v___x_1858_);
                    v___x_1860_ = v___x_1847_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_snd_1845_);
                    v___x_1860_ = v_reuseFailAlloc_1861_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1860_;
            }
            6 => {
                v_fst_1884_ = crate::leanh::lean_ctor_get(v_fst_1879_, 0);
                v_snd_1885_ = crate::leanh::lean_ctor_get(v_fst_1879_, 1);
                v_isSharedCheck_1900_ = (!crate::leanh::lean_is_exclusive(v_fst_1879_)) as u8;
                if v_isSharedCheck_1900_ == 0 {
                    v___x_1887_ = v_fst_1879_;
                    v_isShared_1888_ = v_isSharedCheck_1900_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1885_);
                    crate::leanh::lean_inc(v_fst_1884_);
                    crate::leanh::lean_dec(v_fst_1879_);
                    v___x_1887_ = crate::leanh::lean_box(0);
                    v_isShared_1888_ = v_isSharedCheck_1900_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1898_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_1868_,
                        v_fst_1874_,
                    );
                if v___x_1898_ == 0 {
                    v___y_1890_ = v___x_1898_;
                    state = 8;
                    continue;
                } else {
                    v___x_1899_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1869_,
                            v_fst_1884_,
                        );
                    v___y_1890_ = v___x_1899_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_1890_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1867_);
                    crate::leanh::lean_del_object(v___x_1887_);
                    crate::leanh::lean_del_object(v___x_1882_);
                    crate::leanh::lean_dec_ref_known(v_e_1831_, 3);
                    v___x_1891_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_1867_, v_binderInfo_1870_, v_fst_1874_, v_fst_1884_, v_snd_1885_, v_a_1834_, v_snd_1880_);
                    return v___x_1891_;
                } else {
                    crate::leanh::lean_dec(v_fst_1884_);
                    crate::leanh::lean_dec(v_fst_1874_);
                    if v_isShared_1888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1887_, 0, v_e_1831_);
                        v___x_1893_ = v___x_1887_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1897_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_e_1831_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_snd_1885_);
                        v___x_1893_ = v_reuseFailAlloc_1897_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1893_);
                    v___x_1895_ = v___x_1882_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_snd_1880_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1895_;
            }
            11 => {
                v_fst_1919_ = crate::leanh::lean_ctor_get(v_fst_1914_, 0);
                v_snd_1920_ = crate::leanh::lean_ctor_get(v_fst_1914_, 1);
                v_isSharedCheck_1935_ = (!crate::leanh::lean_is_exclusive(v_fst_1914_)) as u8;
                if v_isSharedCheck_1935_ == 0 {
                    v___x_1922_ = v_fst_1914_;
                    v_isShared_1923_ = v_isSharedCheck_1935_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1920_);
                    crate::leanh::lean_inc(v_fst_1919_);
                    crate::leanh::lean_dec(v_fst_1914_);
                    v___x_1922_ = crate::leanh::lean_box(0);
                    v_isShared_1923_ = v_isSharedCheck_1935_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1933_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_1903_,
                        v_fst_1909_,
                    );
                if v___x_1933_ == 0 {
                    v___y_1925_ = v___x_1933_;
                    state = 13;
                    continue;
                } else {
                    v___x_1934_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1904_,
                            v_fst_1919_,
                        );
                    v___y_1925_ = v___x_1934_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_1925_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1902_);
                    crate::leanh::lean_del_object(v___x_1922_);
                    crate::leanh::lean_del_object(v___x_1917_);
                    crate::leanh::lean_dec_ref_known(v_e_1831_, 3);
                    v___x_1926_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1902_, v_binderInfo_1905_, v_fst_1909_, v_fst_1919_, v_snd_1920_, v_a_1834_, v_snd_1915_);
                    return v___x_1926_;
                } else {
                    crate::leanh::lean_dec(v_fst_1919_);
                    crate::leanh::lean_dec(v_fst_1909_);
                    if v_isShared_1923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1922_, 0, v_e_1831_);
                        v___x_1928_ = v___x_1922_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_e_1831_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_snd_1920_);
                        v___x_1928_ = v_reuseFailAlloc_1932_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1917_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1917_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_snd_1915_);
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1930_;
            }
            16 => {
                v_fst_1960_ = crate::leanh::lean_ctor_get(v_fst_1955_, 0);
                v_snd_1961_ = crate::leanh::lean_ctor_get(v_fst_1955_, 1);
                v_isSharedCheck_1978_ = (!crate::leanh::lean_is_exclusive(v_fst_1955_)) as u8;
                if v_isSharedCheck_1978_ == 0 {
                    v___x_1963_ = v_fst_1955_;
                    v_isShared_1964_ = v_isSharedCheck_1978_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1961_);
                    crate::leanh::lean_inc(v_fst_1960_);
                    crate::leanh::lean_dec(v_fst_1955_);
                    v___x_1963_ = crate::leanh::lean_box(0);
                    v_isShared_1964_ = v_isSharedCheck_1978_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1976_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_1938_,
                        v_fst_1945_,
                    );
                if v___x_1976_ == 0 {
                    v___y_1966_ = v___x_1976_;
                    state = 18;
                    continue;
                } else {
                    v___x_1977_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_1939_,
                            v_fst_1950_,
                        );
                    v___y_1966_ = v___x_1977_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_1966_ == 0 {
                    crate::leanh::lean_inc(v_declName_1937_);
                    crate::leanh::lean_del_object(v___x_1963_);
                    crate::leanh::lean_del_object(v___x_1958_);
                    crate::leanh::lean_dec_ref_known(v_e_1831_, 4);
                    v___x_1967_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1937_, v_fst_1945_, v_fst_1950_, v_fst_1960_, v_nondep_1941_, v_snd_1961_, v_a_1834_, v_snd_1956_);
                    return v___x_1967_;
                } else {
                    v___x_1968_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1940_,
                            v_fst_1960_,
                        );
                    if v___x_1968_ == 0 {
                        crate::leanh::lean_inc(v_declName_1937_);
                        crate::leanh::lean_del_object(v___x_1963_);
                        crate::leanh::lean_del_object(v___x_1958_);
                        crate::leanh::lean_dec_ref_known(v_e_1831_, 4);
                        v___x_1969_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1937_, v_fst_1945_, v_fst_1950_, v_fst_1960_, v_nondep_1941_, v_snd_1961_, v_a_1834_, v_snd_1956_);
                        return v___x_1969_;
                    } else {
                        crate::leanh::lean_dec(v_fst_1960_);
                        crate::leanh::lean_dec(v_fst_1950_);
                        crate::leanh::lean_dec(v_fst_1945_);
                        if v_isShared_1964_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1963_, 0, v_e_1831_);
                            v___x_1971_ = v___x_1963_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1975_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_e_1831_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_snd_1961_);
                            v___x_1971_ = v_reuseFailAlloc_1975_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1958_, 0, v___x_1971_);
                    v___x_1973_ = v___x_1958_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_snd_1956_);
                    v___x_1973_ = v_reuseFailAlloc_1974_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1973_;
            }
            21 => {
                v_fst_1988_ = crate::leanh::lean_ctor_get(v_fst_1983_, 0);
                v_snd_1989_ = crate::leanh::lean_ctor_get(v_fst_1983_, 1);
                v_isSharedCheck_2001_ = (!crate::leanh::lean_is_exclusive(v_fst_1983_)) as u8;
                if v_isSharedCheck_2001_ == 0 {
                    v___x_1991_ = v_fst_1983_;
                    v_isShared_1992_ = v_isSharedCheck_2001_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1989_);
                    crate::leanh::lean_inc(v_fst_1988_);
                    crate::leanh::lean_dec(v_fst_1983_);
                    v___x_1991_ = crate::leanh::lean_box(0);
                    v_isShared_1992_ = v_isSharedCheck_2001_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1993_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_1981_,
                        v_fst_1988_,
                    );
                if v___x_1993_ == 0 {
                    crate::leanh::lean_inc(v_data_1980_);
                    crate::leanh::lean_del_object(v___x_1991_);
                    crate::leanh::lean_del_object(v___x_1986_);
                    crate::leanh::lean_dec_ref_known(v_e_1831_, 2);
                    v___x_1994_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1980_, v_fst_1988_, v_snd_1989_, v_a_1834_, v_snd_1984_);
                    return v___x_1994_;
                } else {
                    crate::leanh::lean_dec(v_fst_1988_);
                    if v_isShared_1992_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1991_, 0, v_e_1831_);
                        v___x_1996_ = v___x_1991_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_e_1831_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_snd_1989_);
                        v___x_1996_ = v_reuseFailAlloc_2000_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1986_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1986_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_snd_1984_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1998_;
            }
            25 => {
                v_fst_2012_ = crate::leanh::lean_ctor_get(v_fst_2007_, 0);
                v_snd_2013_ = crate::leanh::lean_ctor_get(v_fst_2007_, 1);
                v_isSharedCheck_2025_ = (!crate::leanh::lean_is_exclusive(v_fst_2007_)) as u8;
                if v_isSharedCheck_2025_ == 0 {
                    v___x_2015_ = v_fst_2007_;
                    v_isShared_2016_ = v_isSharedCheck_2025_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2013_);
                    crate::leanh::lean_inc(v_fst_2012_);
                    crate::leanh::lean_dec(v_fst_2007_);
                    v___x_2015_ = crate::leanh::lean_box(0);
                    v_isShared_2016_ = v_isSharedCheck_2025_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2017_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_2005_,
                        v_fst_2012_,
                    );
                if v___x_2017_ == 0 {
                    crate::leanh::lean_inc(v_idx_2004_);
                    crate::leanh::lean_inc(v_typeName_2003_);
                    crate::leanh::lean_del_object(v___x_2015_);
                    crate::leanh::lean_del_object(v___x_2010_);
                    crate::leanh::lean_dec_ref_known(v_e_1831_, 3);
                    v___x_2018_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_2003_, v_idx_2004_, v_fst_2012_, v_snd_2013_, v_a_1834_, v_snd_2008_);
                    return v___x_2018_;
                } else {
                    crate::leanh::lean_dec(v_fst_2012_);
                    if v_isShared_2016_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2015_, 0, v_e_1831_);
                        v___x_2020_ = v___x_2015_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2024_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_e_1831_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_snd_2013_);
                        v___x_2020_ = v_reuseFailAlloc_2024_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_2020_);
                    v___x_2022_ = v___x_2010_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_snd_2008_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(
    mut v_s_2029_: *mut crate::leanh::LeanObject,
    mut v_d_2030_: *mut crate::leanh::LeanObject,
    mut v_e_2031_: *mut crate::leanh::LeanObject,
    mut v_offset_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: u8,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_u2081_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v_deBruijnIndex_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_offset_2032_);
                crate::leanh::lean_inc_ref(v_e_2031_);
                v_key_2036_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_key_2036_, 0, v_e_2031_);
                crate::leanh::lean_ctor_set(v_key_2036_, 1, v_offset_2032_);
                v___x_2051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_2033_, v_key_2036_);
                if crate::leanh::lean_obj_tag(v___x_2051_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_key_2036_, 2);
                    crate::leanh::lean_dec(v_offset_2032_);
                    crate::leanh::lean_dec_ref(v_e_2031_);
                    v_val_2052_ = crate::leanh::lean_ctor_get(v___x_2051_, 0);
                    crate::leanh::lean_inc(v_val_2052_);
                    crate::leanh::lean_dec_ref_known(v___x_2051_, 1);
                    v___x_2053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2053_, 0, v_val_2052_);
                    crate::leanh::lean_ctor_set(v___x_2053_, 1, v_a_2033_);
                    v___x_2054_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2053_);
                    crate::leanh::lean_ctor_set(v___x_2054_, 1, v_a_2035_);
                    return v___x_2054_;
                } else {
                    crate::leanh::lean_dec(v___x_2051_);
                    v_s_u2081_2055_ = lean_nat_add(v_s_2029_, v_offset_2032_);
                    v___x_2056_ = l_Lean_Expr_looseBVarRange(v_e_2031_);
                    v___x_2057_ = lean_nat_dec_le(v___x_2056_, v_s_u2081_2055_);
                    crate::leanh::lean_dec(v___x_2056_);
                    if v___x_2057_ == 0 {
                        if crate::leanh::lean_obj_tag(v_e_2031_) == 0 {
                            v_deBruijnIndex_2058_ = crate::leanh::lean_ctor_get(v_e_2031_, 0);
                            v___x_2059_ = lean_nat_dec_le(v_s_u2081_2055_, v_deBruijnIndex_2058_);
                            crate::leanh::lean_dec(v_s_u2081_2055_);
                            if v___x_2059_ == 0 {
                                v_snd_2038_ = v_a_2035_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_deBruijnIndex_2058_);
                                crate::leanh::lean_dec_ref_known(v_e_2031_, 1);
                                crate::leanh::lean_dec(v_offset_2032_);
                                v___x_2060_ = lean_nat_add(v_deBruijnIndex_2058_, v_d_2030_);
                                crate::leanh::lean_dec(v_deBruijnIndex_2058_);
                                v___x_2061_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_2060_, v_a_2035_);
                                v_fst_2062_ = crate::leanh::lean_ctor_get(v___x_2061_, 0);
                                crate::leanh::lean_inc(v_fst_2062_);
                                v_snd_2063_ = crate::leanh::lean_ctor_get(v___x_2061_, 1);
                                crate::leanh::lean_inc(v_snd_2063_);
                                crate::leanh::lean_dec_ref(v___x_2061_);
                                v___x_2064_ =
                                    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                        v_key_2036_,
                                        v_fst_2062_,
                                        v_a_2033_,
                                        v_a_2034_,
                                        v_snd_2063_,
                                    );
                                return v___x_2064_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_s_u2081_2055_);
                            v_snd_2038_ = v_a_2035_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_s_u2081_2055_);
                        crate::leanh::lean_dec(v_offset_2032_);
                        v___x_2065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_2036_,
                            v_e_2031_,
                            v_a_2033_,
                            v_a_2034_,
                            v_a_2035_,
                        );
                        return v___x_2065_;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_e_2031_) {
                9 => {
                    crate::leanh::lean_dec(v_offset_2032_);
                    v___x_2039_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_e_2031_,
                        v_a_2033_,
                        v_a_2034_,
                        v_snd_2038_,
                    );
                    return v___x_2039_;
                }
                2 => {
                    crate::leanh::lean_dec(v_offset_2032_);
                    v___x_2040_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_e_2031_,
                        v_a_2033_,
                        v_a_2034_,
                        v_snd_2038_,
                    );
                    return v___x_2040_;
                }
                0 => {
                    crate::leanh::lean_dec(v_offset_2032_);
                    v___x_2041_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_e_2031_,
                        v_a_2033_,
                        v_a_2034_,
                        v_snd_2038_,
                    );
                    return v___x_2041_;
                }
                1 => {
                    crate::leanh::lean_dec(v_offset_2032_);
                    v___x_2042_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_e_2031_,
                        v_a_2033_,
                        v_a_2034_,
                        v_snd_2038_,
                    );
                    return v___x_2042_;
                }
                4 => {
                    crate::leanh::lean_dec(v_offset_2032_);
                    v___x_2043_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_e_2031_,
                        v_a_2033_,
                        v_a_2034_,
                        v_snd_2038_,
                    );
                    return v___x_2043_;
                }
                3 => {
                    crate::leanh::lean_dec(v_offset_2032_);
                    v___x_2044_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_e_2031_,
                        v_a_2033_,
                        v_a_2034_,
                        v_snd_2038_,
                    );
                    return v___x_2044_;
                }
                _ => {
                    v___x_2045_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_2029_, v_d_2030_, v_e_2031_, v_offset_2032_, v_a_2033_, v_a_2034_, v_snd_2038_);
                    v_fst_2046_ = crate::leanh::lean_ctor_get(v___x_2045_, 0);
                    crate::leanh::lean_inc(v_fst_2046_);
                    v_snd_2047_ = crate::leanh::lean_ctor_get(v___x_2045_, 1);
                    crate::leanh::lean_inc(v_snd_2047_);
                    crate::leanh::lean_dec_ref(v___x_2045_);
                    v_fst_2048_ = crate::leanh::lean_ctor_get(v_fst_2046_, 0);
                    crate::leanh::lean_inc(v_fst_2048_);
                    v_snd_2049_ = crate::leanh::lean_ctor_get(v_fst_2046_, 1);
                    crate::leanh::lean_inc(v_snd_2049_);
                    crate::leanh::lean_dec(v_fst_2046_);
                    v___x_2050_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2036_,
                        v_fst_2048_,
                        v_snd_2049_,
                        v_a_2034_,
                        v_snd_2047_,
                    );
                    return v___x_2050_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(
    mut v_s_2066_: *mut crate::leanh::LeanObject,
    mut v_d_2067_: *mut crate::leanh::LeanObject,
    mut v_e_2068_: *mut crate::leanh::LeanObject,
    mut v_offset_2069_: *mut crate::leanh::LeanObject,
    mut v_a_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2073_: u8 = 0;
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2073_ = (crate::leanh::lean_unbox(v_a_2071_) as u8);
    v_res_2074_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_2066_, v_d_2067_, v_e_2068_, v_offset_2069_, v_a_2070_, v_a_boxed_2073_, v_a_2072_);
    crate::leanh::lean_dec(v_d_2067_);
    crate::leanh::lean_dec(v_s_2066_);
    return v_res_2074_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(
    mut v_s_2075_: *mut crate::leanh::LeanObject,
    mut v_d_2076_: *mut crate::leanh::LeanObject,
    mut v_e_2077_: *mut crate::leanh::LeanObject,
    mut v_offset_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2082_: u8 = 0;
    let mut v_res_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2082_ = (crate::leanh::lean_unbox(v_a_2080_) as u8);
    v_res_2083_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_2075_, v_d_2076_, v_e_2077_, v_offset_2078_, v_a_2079_, v_a_boxed_2082_, v_a_2081_);
    crate::leanh::lean_dec(v_d_2076_);
    crate::leanh::lean_dec(v_s_2075_);
    return v_res_2083_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS_x27(
    mut v_e_2084_: *mut crate::leanh::LeanObject,
    mut v_s_2085_: *mut crate::leanh::LeanObject,
    mut v_d_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: u8,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: u8 = 0;
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_unused_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2089_ = l_Lean_Expr_looseBVarRange(v_e_2084_);
                v___x_2090_ = lean_nat_dec_le(v___x_2089_, v_s_2085_);
                crate::leanh::lean_dec(v___x_2089_);
                if v___x_2090_ == 0 {
                    v___x_2091_ = crate::leanh::lean_unsigned_to_nat(0);
                    if crate::leanh::lean_obj_tag(v_e_2084_) == 0 {
                        v_deBruijnIndex_2113_ = crate::leanh::lean_ctor_get(v_e_2084_, 0);
                        v___x_2114_ = lean_nat_dec_le(v_s_2085_, v_deBruijnIndex_2113_);
                        if v___x_2114_ == 0 {
                            v_snd_2093_ = v_a_2088_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_deBruijnIndex_2113_);
                            crate::leanh::lean_dec_ref_known(v_e_2084_, 1);
                            v___x_2115_ = lean_nat_add(v_deBruijnIndex_2113_, v_d_2086_);
                            crate::leanh::lean_dec(v_deBruijnIndex_2113_);
                            v___x_2116_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_2115_, v_a_2088_);
                            return v___x_2116_;
                        }
                    } else {
                        v_snd_2093_ = v_a_2088_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2117_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2117_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2117_, 1, v_a_2088_);
                    return v___x_2117_;
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_e_2084_) {
                9 => {
                    v___x_2094_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2094_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2094_, 1, v_snd_2093_);
                    return v___x_2094_;
                }
                2 => {
                    v___x_2095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2095_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2095_, 1, v_snd_2093_);
                    return v___x_2095_;
                }
                0 => {
                    v___x_2096_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2096_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2096_, 1, v_snd_2093_);
                    return v___x_2096_;
                }
                1 => {
                    v___x_2097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2097_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2097_, 1, v_snd_2093_);
                    return v___x_2097_;
                }
                4 => {
                    v___x_2098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2098_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2098_, 1, v_snd_2093_);
                    return v___x_2098_;
                }
                3 => {
                    v___x_2099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2099_, 0, v_e_2084_);
                    crate::leanh::lean_ctor_set(v___x_2099_, 1, v_snd_2093_);
                    return v___x_2099_;
                }
                _ => {
                    v___x_2100_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1,
                    );
                    v___x_2101_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_2085_, v_d_2086_, v_e_2084_, v___x_2091_, v___x_2100_, v_a_2087_, v_snd_2093_);
                    v_fst_2102_ = crate::leanh::lean_ctor_get(v___x_2101_, 0);
                    crate::leanh::lean_inc(v_fst_2102_);
                    v_snd_2103_ = crate::leanh::lean_ctor_get(v___x_2101_, 1);
                    crate::leanh::lean_inc(v_snd_2103_);
                    crate::leanh::lean_dec_ref(v___x_2101_);
                    v_fst_2104_ = crate::leanh::lean_ctor_get(v_fst_2102_, 0);
                    v_isSharedCheck_2111_ = (!crate::leanh::lean_is_exclusive(v_fst_2102_)) as u8;
                    if v_isSharedCheck_2111_ == 0 {
                        v_unused_2112_ = crate::leanh::lean_ctor_get(v_fst_2102_, 1);
                        crate::leanh::lean_dec(v_unused_2112_);
                        v___x_2106_ = v_fst_2102_;
                        v_isShared_2107_ = v_isSharedCheck_2111_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2104_);
                        crate::leanh::lean_dec(v_fst_2102_);
                        v___x_2106_ = crate::leanh::lean_box(0);
                        v_isShared_2107_ = v_isSharedCheck_2111_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => {
                if v_isShared_2107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2106_, 1, v_snd_2103_);
                    v___x_2109_ = v___x_2106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fst_2104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2103_);
                    v___x_2109_ = v_reuseFailAlloc_2110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(
    mut v_e_2118_: *mut crate::leanh::LeanObject,
    mut v_s_2119_: *mut crate::leanh::LeanObject,
    mut v_d_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2123_: u8 = 0;
    let mut v_res_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2123_ = (crate::leanh::lean_unbox(v_a_2121_) as u8);
    v_res_2124_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
        v_e_2118_,
        v_s_2119_,
        v_d_2120_,
        v_a_boxed_2123_,
        v_a_2122_,
    );
    crate::leanh::lean_dec(v_d_2120_);
    crate::leanh::lean_dec(v_s_2119_);
    return v_res_2124_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS___redArg(
    mut v_e_2125_: *mut crate::leanh::LeanObject,
    mut v_s_2126_: *mut crate::leanh::LeanObject,
    mut v_d_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2141_: u8 = 0;
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2150_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2164_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_unused_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2130_ = lean_st_ref_take(v_a_2128_);
                v_share_2131_ = crate::leanh::lean_ctor_get(v___x_2130_, 0);
                v_maxFVar_2132_ = crate::leanh::lean_ctor_get(v___x_2130_, 1);
                v_proofInstInfo_2133_ = crate::leanh::lean_ctor_get(v___x_2130_, 2);
                v_inferType_2134_ = crate::leanh::lean_ctor_get(v___x_2130_, 3);
                v_getLevel_2135_ = crate::leanh::lean_ctor_get(v___x_2130_, 4);
                v_congrInfo_2136_ = crate::leanh::lean_ctor_get(v___x_2130_, 5);
                v_defEqI_2137_ = crate::leanh::lean_ctor_get(v___x_2130_, 6);
                v_extensions_2138_ = crate::leanh::lean_ctor_get(v___x_2130_, 7);
                v_issues_2139_ = crate::leanh::lean_ctor_get(v___x_2130_, 8);
                v_canon_2140_ = crate::leanh::lean_ctor_get(v___x_2130_, 9);
                v_debug_2141_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2130_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v___x_2130_)) as u8;
                if v_isSharedCheck_2176_ == 0 {
                    v___x_2143_ = v___x_2130_;
                    v_isShared_2144_ = v_isSharedCheck_2176_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_2140_);
                    crate::leanh::lean_inc(v_issues_2139_);
                    crate::leanh::lean_inc(v_extensions_2138_);
                    crate::leanh::lean_inc(v_defEqI_2137_);
                    crate::leanh::lean_inc(v_congrInfo_2136_);
                    crate::leanh::lean_inc(v_getLevel_2135_);
                    crate::leanh::lean_inc(v_inferType_2134_);
                    crate::leanh::lean_inc(v_proofInstInfo_2133_);
                    crate::leanh::lean_inc(v_maxFVar_2132_);
                    crate::leanh::lean_inc(v_share_2131_);
                    crate::leanh::lean_dec(v___x_2130_);
                    v___x_2143_ = crate::leanh::lean_box(0);
                    v_isShared_2144_ = v_isSharedCheck_2176_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2145_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0,
                );
                if v_isShared_2144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2175_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_maxFVar_2132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_proofInstInfo_2133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_inferType_2134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_getLevel_2135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_congrInfo_2136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_defEqI_2137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_extensions_2138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_issues_2139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 9, v_canon_2140_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2175_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_2141_,
                    );
                    v___x_2147_ = v_reuseFailAlloc_2175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2148_ = lean_st_ref_set(v_a_2128_, v___x_2147_);
                v___x_2149_ = lean_st_ref_get(v_a_2128_);
                v_debug_2150_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2149_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_2149_);
                v___x_2151_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                    v_e_2125_,
                    v_s_2126_,
                    v_d_2127_,
                    v_debug_2150_,
                    v_share_2131_,
                );
                v_fst_2152_ = crate::leanh::lean_ctor_get(v___x_2151_, 0);
                crate::leanh::lean_inc(v_fst_2152_);
                v_snd_2153_ = crate::leanh::lean_ctor_get(v___x_2151_, 1);
                crate::leanh::lean_inc(v_snd_2153_);
                crate::leanh::lean_dec_ref(v___x_2151_);
                v___x_2154_ = lean_st_ref_take(v_a_2128_);
                v_maxFVar_2155_ = crate::leanh::lean_ctor_get(v___x_2154_, 1);
                v_proofInstInfo_2156_ = crate::leanh::lean_ctor_get(v___x_2154_, 2);
                v_inferType_2157_ = crate::leanh::lean_ctor_get(v___x_2154_, 3);
                v_getLevel_2158_ = crate::leanh::lean_ctor_get(v___x_2154_, 4);
                v_congrInfo_2159_ = crate::leanh::lean_ctor_get(v___x_2154_, 5);
                v_defEqI_2160_ = crate::leanh::lean_ctor_get(v___x_2154_, 6);
                v_extensions_2161_ = crate::leanh::lean_ctor_get(v___x_2154_, 7);
                v_issues_2162_ = crate::leanh::lean_ctor_get(v___x_2154_, 8);
                v_canon_2163_ = crate::leanh::lean_ctor_get(v___x_2154_, 9);
                v_debug_2164_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2154_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2173_ = (!crate::leanh::lean_is_exclusive(v___x_2154_)) as u8;
                if v_isSharedCheck_2173_ == 0 {
                    v_unused_2174_ = crate::leanh::lean_ctor_get(v___x_2154_, 0);
                    crate::leanh::lean_dec(v_unused_2174_);
                    v___x_2166_ = v___x_2154_;
                    v_isShared_2167_ = v_isSharedCheck_2173_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_2163_);
                    crate::leanh::lean_inc(v_issues_2162_);
                    crate::leanh::lean_inc(v_extensions_2161_);
                    crate::leanh::lean_inc(v_defEqI_2160_);
                    crate::leanh::lean_inc(v_congrInfo_2159_);
                    crate::leanh::lean_inc(v_getLevel_2158_);
                    crate::leanh::lean_inc(v_inferType_2157_);
                    crate::leanh::lean_inc(v_proofInstInfo_2156_);
                    crate::leanh::lean_inc(v_maxFVar_2155_);
                    crate::leanh::lean_dec(v___x_2154_);
                    v___x_2166_ = crate::leanh::lean_box(0);
                    v_isShared_2167_ = v_isSharedCheck_2173_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2166_, 0, v_snd_2153_);
                    v___x_2169_ = v___x_2166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_snd_2153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_maxFVar_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_proofInstInfo_2156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_inferType_2157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_getLevel_2158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_congrInfo_2159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_defEqI_2160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_extensions_2161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_issues_2162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 9, v_canon_2163_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2172_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_2164_,
                    );
                    v___x_2169_ = v_reuseFailAlloc_2172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2170_ = lean_st_ref_set(v_a_2128_, v___x_2169_);
                v___x_2171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2171_, 0, v_fst_2152_);
                return v___x_2171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS___redArg___boxed(
    mut v_e_2177_: *mut crate::leanh::LeanObject,
    mut v_s_2178_: *mut crate::leanh::LeanObject,
    mut v_d_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2182_ =
        l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_2177_, v_s_2178_, v_d_2179_, v_a_2180_);
    crate::leanh::lean_dec(v_a_2180_);
    crate::leanh::lean_dec(v_d_2179_);
    crate::leanh::lean_dec(v_s_2178_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS(
    mut v_e_2183_: *mut crate::leanh::LeanObject,
    mut v_s_2184_: *mut crate::leanh::LeanObject,
    mut v_d_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
    mut v_a_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ =
        l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_2183_, v_s_2184_, v_d_2185_, v_a_2187_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS___boxed(
    mut v_e_2194_: *mut crate::leanh::LeanObject,
    mut v_s_2195_: *mut crate::leanh::LeanObject,
    mut v_d_2196_: *mut crate::leanh::LeanObject,
    mut v_a_2197_: *mut crate::leanh::LeanObject,
    mut v_a_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l_Lean_Meta_Sym_liftLooseBVarsS(
        v_e_2194_, v_s_2195_, v_d_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_,
        v_a_2202_,
    );
    crate::leanh::lean_dec(v_a_2202_);
    crate::leanh::lean_dec_ref(v_a_2201_);
    crate::leanh::lean_dec(v_a_2200_);
    crate::leanh::lean_dec_ref(v_a_2199_);
    crate::leanh::lean_dec(v_a_2198_);
    crate::leanh::lean_dec_ref(v_a_2197_);
    crate::leanh::lean_dec(v_d_2196_);
    crate::leanh::lean_dec(v_s_2195_);
    return v_res_2204_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_LooseBVarsS(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_LooseBVarsS(
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
pub unsafe fn initialize_Lean_Meta_Sym_LooseBVarsS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
}
