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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(
    mut v_idx_1103_: *mut LeanObject,
    mut v___y_1104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lean_Expr_bvar___override(v_idx_1103_);
    v___x_1106_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1105_, v___y_1104_);
    return v___x_1106_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(
    mut v_idx_1107_: *mut LeanObject,
    mut v___y_1108_: u8,
    mut v___y_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v_idx_1107_, v___y_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(
    mut v_idx_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21034__boxed_1114_: u8 = 0;
    let mut v_res_1115_: *mut LeanObject = core::ptr::null_mut();
    v___y_21034__boxed_1114_ = (lean_unbox(v___y_1112_) as u8);
    v_res_1115_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(
            v_idx_1111_,
            v___y_21034__boxed_1114_,
            v___y_1113_,
        );
    return v_res_1115_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(
    mut v_x_1116_: *mut LeanObject,
    mut v_bi_1117_: u8,
    mut v_t_1118_: *mut LeanObject,
    mut v_b_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: u8,
    mut v___y_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1141_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_1118_);
                    v___x_1138_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1118_,
                        v___y_1121_,
                        v___y_1122_,
                    );
                    v_snd_1139_ = lean_ctor_get(v___x_1138_, 1);
                    lean_inc(v_snd_1139_);
                    lean_dec_ref(v___x_1138_);
                    lean_inc_ref(v_b_1119_);
                    v___x_1140_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1119_,
                        v___y_1121_,
                        v_snd_1139_,
                    );
                    v_snd_1141_ = lean_ctor_get(v___x_1140_, 1);
                    lean_inc(v_snd_1141_);
                    lean_dec_ref(v___x_1140_);
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
                v_fst_1128_ = lean_ctor_get(v___x_1127_, 0);
                v_snd_1129_ = lean_ctor_get(v___x_1127_, 1);
                v_isSharedCheck_1137_ = (!lean_is_exclusive(v___x_1127_)) as u8;
                if v_isSharedCheck_1137_ == 0 {
                    v___x_1131_ = v___x_1127_;
                    v_isShared_1132_ = v_isSharedCheck_1137_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1129_);
                    lean_inc(v_fst_1128_);
                    lean_dec(v___x_1127_);
                    v___x_1131_ = lean_box(0);
                    v_isShared_1132_ = v_isSharedCheck_1137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1132_ == 0 {
                    lean_ctor_set(v___x_1131_, 1, v___y_1124_);
                    v___x_1134_ = v___x_1131_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_fst_1128_);
                    lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___y_1124_);
                    v___x_1134_ = v_reuseFailAlloc_1136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1135_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1135_, 0, v___x_1134_);
                lean_ctor_set(v___x_1135_, 1, v_snd_1129_);
                return v___x_1135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(
    mut v_x_1142_: *mut LeanObject,
    mut v_bi_1143_: *mut LeanObject,
    mut v_t_1144_: *mut LeanObject,
    mut v_b_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1149_: u8 = 0;
    let mut v___y_21043__boxed_1150_: u8 = 0;
    let mut v_res_1151_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1149_ = (lean_unbox(v_bi_1143_) as u8);
    v___y_21043__boxed_1150_ = (lean_unbox(v___y_1147_) as u8);
    v_res_1151_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_1142_, v_bi_boxed_1149_, v_t_1144_, v_b_1145_, v___y_1146_, v___y_21043__boxed_1150_, v___y_1148_);
    return v_res_1151_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(
    mut v_structName_1152_: *mut LeanObject,
    mut v_idx_1153_: *mut LeanObject,
    mut v_struct_1154_: *mut LeanObject,
    mut v___y_1155_: *mut LeanObject,
    mut v___y_1156_: u8,
    mut v___y_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1174_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_struct_1154_);
                    v___x_1173_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_1154_,
                        v___y_1156_,
                        v___y_1157_,
                    );
                    v_snd_1174_ = lean_ctor_get(v___x_1173_, 1);
                    lean_inc(v_snd_1174_);
                    lean_dec_ref(v___x_1173_);
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
                v_fst_1163_ = lean_ctor_get(v___x_1162_, 0);
                v_snd_1164_ = lean_ctor_get(v___x_1162_, 1);
                v_isSharedCheck_1172_ = (!lean_is_exclusive(v___x_1162_)) as u8;
                if v_isSharedCheck_1172_ == 0 {
                    v___x_1166_ = v___x_1162_;
                    v_isShared_1167_ = v_isSharedCheck_1172_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1164_);
                    lean_inc(v_fst_1163_);
                    lean_dec(v___x_1162_);
                    v___x_1166_ = lean_box(0);
                    v_isShared_1167_ = v_isSharedCheck_1172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1167_ == 0 {
                    lean_ctor_set(v___x_1166_, 1, v___y_1159_);
                    v___x_1169_ = v___x_1166_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_fst_1163_);
                    lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___y_1159_);
                    v___x_1169_ = v_reuseFailAlloc_1171_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1170_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                lean_ctor_set(v___x_1170_, 1, v_snd_1164_);
                return v___x_1170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(
    mut v_structName_1175_: *mut LeanObject,
    mut v_idx_1176_: *mut LeanObject,
    mut v_struct_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21092__boxed_1181_: u8 = 0;
    let mut v_res_1182_: *mut LeanObject = core::ptr::null_mut();
    v___y_21092__boxed_1181_ = (lean_unbox(v___y_1179_) as u8);
    v_res_1182_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_1175_, v_idx_1176_, v_struct_1177_, v___y_1178_, v___y_21092__boxed_1181_, v___y_1180_);
    return v_res_1182_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(
    mut v_x_1183_: *mut LeanObject,
    mut v_bi_1184_: u8,
    mut v_t_1185_: *mut LeanObject,
    mut v_b_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: u8,
    mut v___y_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1199_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1204_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1208_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_1185_);
                    v___x_1205_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1185_,
                        v___y_1188_,
                        v___y_1189_,
                    );
                    v_snd_1206_ = lean_ctor_get(v___x_1205_, 1);
                    lean_inc(v_snd_1206_);
                    lean_dec_ref(v___x_1205_);
                    lean_inc_ref(v_b_1186_);
                    v___x_1207_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1186_,
                        v___y_1188_,
                        v_snd_1206_,
                    );
                    v_snd_1208_ = lean_ctor_get(v___x_1207_, 1);
                    lean_inc(v_snd_1208_);
                    lean_dec_ref(v___x_1207_);
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
                v_fst_1195_ = lean_ctor_get(v___x_1194_, 0);
                v_snd_1196_ = lean_ctor_get(v___x_1194_, 1);
                v_isSharedCheck_1204_ = (!lean_is_exclusive(v___x_1194_)) as u8;
                if v_isSharedCheck_1204_ == 0 {
                    v___x_1198_ = v___x_1194_;
                    v_isShared_1199_ = v_isSharedCheck_1204_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1196_);
                    lean_inc(v_fst_1195_);
                    lean_dec(v___x_1194_);
                    v___x_1198_ = lean_box(0);
                    v_isShared_1199_ = v_isSharedCheck_1204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1199_ == 0 {
                    lean_ctor_set(v___x_1198_, 1, v___y_1191_);
                    v___x_1201_ = v___x_1198_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_fst_1195_);
                    lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___y_1191_);
                    v___x_1201_ = v_reuseFailAlloc_1203_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1202_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1202_, 0, v___x_1201_);
                lean_ctor_set(v___x_1202_, 1, v_snd_1196_);
                return v___x_1202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(
    mut v_x_1209_: *mut LeanObject,
    mut v_bi_1210_: *mut LeanObject,
    mut v_t_1211_: *mut LeanObject,
    mut v_b_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1216_: u8 = 0;
    let mut v___y_21136__boxed_1217_: u8 = 0;
    let mut v_res_1218_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1216_ = (lean_unbox(v_bi_1210_) as u8);
    v___y_21136__boxed_1217_ = (lean_unbox(v___y_1214_) as u8);
    v_res_1218_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_1209_, v_bi_boxed_1216_, v_t_1211_, v_b_1212_, v___y_1213_, v___y_21136__boxed_1217_, v___y_1215_);
    return v_res_1218_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(
    mut v_msg_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: u8,
    mut v___y_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_20767__overap_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___f_1230_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0;
    v___f_1231_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1;
    v___f_1232_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2;
    v___f_1233_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3;
    v___f_1234_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4;
    v___f_1235_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5;
    v___f_1236_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6;
    v___x_1237_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1237_, 0, v___f_1230_);
    lean_ctor_set(v___x_1237_, 1, v___f_1231_);
    v___x_1238_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    lean_ctor_set(v___x_1238_, 1, v___f_1232_);
    lean_ctor_set(v___x_1238_, 2, v___f_1233_);
    lean_ctor_set(v___x_1238_, 3, v___f_1234_);
    lean_ctor_set(v___x_1238_, 4, v___f_1235_);
    v___x_1239_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    lean_ctor_set(v___x_1239_, 1, v___f_1236_);
    lean_inc_ref_n(v___x_1239_, 6);
    v___f_1240_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1240_, 0, v___x_1239_);
    v___f_1241_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1241_, 0, v___x_1239_);
    v___f_1242_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1242_, 0, v___x_1239_);
    v___f_1243_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1243_, 0, v___x_1239_);
    v___x_1244_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1244_, 0, lean_box(0));
    lean_closure_set(v___x_1244_, 1, lean_box(0));
    lean_closure_set(v___x_1244_, 2, v___x_1239_);
    v___x_1245_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1245_, 0, v___x_1244_);
    lean_ctor_set(v___x_1245_, 1, v___f_1240_);
    v___x_1246_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1246_, 0, lean_box(0));
    lean_closure_set(v___x_1246_, 1, lean_box(0));
    lean_closure_set(v___x_1246_, 2, v___x_1239_);
    v___x_1247_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1247_, 0, v___x_1245_);
    lean_ctor_set(v___x_1247_, 1, v___x_1246_);
    lean_ctor_set(v___x_1247_, 2, v___f_1241_);
    lean_ctor_set(v___x_1247_, 3, v___f_1242_);
    lean_ctor_set(v___x_1247_, 4, v___f_1243_);
    v___x_1248_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1248_, 0, lean_box(0));
    lean_closure_set(v___x_1248_, 1, lean_box(0));
    lean_closure_set(v___x_1248_, 2, v___x_1239_);
    v___x_1249_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1249_, 0, v___x_1247_);
    lean_ctor_set(v___x_1249_, 1, v___x_1248_);
    v___x_1250_ = l_ReaderT_instMonad___redArg(v___x_1249_);
    lean_inc_ref_n(v___x_1250_, 6);
    v___f_1251_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1251_, 0, v___x_1250_);
    v___f_1252_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1252_, 0, v___x_1250_);
    v___f_1253_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1253_, 0, v___x_1250_);
    v___f_1254_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1254_, 0, v___x_1250_);
    v___x_1255_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1255_, 0, lean_box(0));
    lean_closure_set(v___x_1255_, 1, lean_box(0));
    lean_closure_set(v___x_1255_, 2, v___x_1250_);
    v___x_1256_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1256_, 0, v___x_1255_);
    lean_ctor_set(v___x_1256_, 1, v___f_1251_);
    v___x_1257_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1257_, 0, lean_box(0));
    lean_closure_set(v___x_1257_, 1, lean_box(0));
    lean_closure_set(v___x_1257_, 2, v___x_1250_);
    v___x_1258_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1258_, 0, v___x_1256_);
    lean_ctor_set(v___x_1258_, 1, v___x_1257_);
    lean_ctor_set(v___x_1258_, 2, v___f_1252_);
    lean_ctor_set(v___x_1258_, 3, v___f_1253_);
    lean_ctor_set(v___x_1258_, 4, v___f_1254_);
    v___x_1259_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1259_, 0, lean_box(0));
    lean_closure_set(v___x_1259_, 1, lean_box(0));
    lean_closure_set(v___x_1259_, 2, v___x_1250_);
    v___x_1260_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1260_, 0, v___x_1258_);
    lean_ctor_set(v___x_1260_, 1, v___x_1259_);
    v___x_1261_ = l_Lean_instInhabitedExpr;
    v___x_1262_ = l_instInhabitedOfMonad___redArg(v___x_1260_, v___x_1261_);
    v___x_20767__overap_1263_ = lean_panic_fn_borrowed(v___x_1262_, v_msg_1226_);
    lean_dec(v___x_1262_);
    v___x_1264_ = lean_box((v___y_1228_) as usize);
    v___x_1265_ = lean_apply_3(
        v___x_20767__overap_1263_,
        v___y_1227_,
        v___x_1264_,
        v___y_1229_,
    );
    return v___x_1265_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(
    mut v_msg_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21199__boxed_1270_: u8 = 0;
    let mut v_res_1271_: *mut LeanObject = core::ptr::null_mut();
    v___y_21199__boxed_1270_ = (lean_unbox(v___y_1268_) as u8);
    v_res_1271_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_1266_, v___y_1267_, v___y_21199__boxed_1270_, v___y_1269_);
    return v_res_1271_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(
    mut v_f_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: u8,
    mut v___y_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1295_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_f_1272_);
                    v___x_1292_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_1272_,
                        v___y_1275_,
                        v___y_1276_,
                    );
                    v_snd_1293_ = lean_ctor_get(v___x_1292_, 1);
                    lean_inc(v_snd_1293_);
                    lean_dec_ref(v___x_1292_);
                    lean_inc_ref(v_a_1273_);
                    v___x_1294_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_1273_,
                        v___y_1275_,
                        v_snd_1293_,
                    );
                    v_snd_1295_ = lean_ctor_get(v___x_1294_, 1);
                    lean_inc(v_snd_1295_);
                    lean_dec_ref(v___x_1294_);
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
                v_fst_1282_ = lean_ctor_get(v___x_1281_, 0);
                v_snd_1283_ = lean_ctor_get(v___x_1281_, 1);
                v_isSharedCheck_1291_ = (!lean_is_exclusive(v___x_1281_)) as u8;
                if v_isSharedCheck_1291_ == 0 {
                    v___x_1285_ = v___x_1281_;
                    v_isShared_1286_ = v_isSharedCheck_1291_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1283_);
                    lean_inc(v_fst_1282_);
                    lean_dec(v___x_1281_);
                    v___x_1285_ = lean_box(0);
                    v_isShared_1286_ = v_isSharedCheck_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1286_ == 0 {
                    lean_ctor_set(v___x_1285_, 1, v___y_1278_);
                    v___x_1288_ = v___x_1285_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_fst_1282_);
                    lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___y_1278_);
                    v___x_1288_ = v_reuseFailAlloc_1290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1289_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1289_, 0, v___x_1288_);
                lean_ctor_set(v___x_1289_, 1, v_snd_1283_);
                return v___x_1289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(
    mut v_f_1296_: *mut LeanObject,
    mut v_a_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21285__boxed_1301_: u8 = 0;
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v___y_21285__boxed_1301_ = (lean_unbox(v___y_1299_) as u8);
    v_res_1302_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_1296_, v_a_1297_, v___y_1298_, v___y_21285__boxed_1301_, v___y_1300_);
    return v_res_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(
    mut v_a_1303_: *mut LeanObject,
    mut v_x_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1310_: u8 = 0;
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1304_) == 0 {
                    v___x_1305_ = lean_box(0);
                    return v___x_1305_;
                } else {
                    v_key_1306_ = lean_ctor_get(v_x_1304_, 0);
                    v_value_1307_ = lean_ctor_get(v_x_1304_, 1);
                    v_tail_1308_ = lean_ctor_get(v_x_1304_, 2);
                    v_fst_1313_ = lean_ctor_get(v_key_1306_, 0);
                    v_snd_1314_ = lean_ctor_get(v_key_1306_, 1);
                    v_fst_1315_ = lean_ctor_get(v_a_1303_, 0);
                    v_snd_1316_ = lean_ctor_get(v_a_1303_, 1);
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
                    lean_inc(v_value_1307_);
                    v___x_1312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1312_, 0, v_value_1307_);
                    return v___x_1312_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(
    mut v_a_1319_: *mut LeanObject,
    mut v_x_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1321_: *mut LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_1319_, v_x_1320_);
    lean_dec(v_x_1320_);
    lean_dec_ref(v_a_1319_);
    return v_res_1321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(
    mut v_m_1322_: *mut LeanObject,
    mut v_a_1323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1324_ = lean_ctor_get(v_m_1322_, 1);
    v_fst_1325_ = lean_ctor_get(v_a_1323_, 0);
    v_snd_1326_ = lean_ctor_get(v_a_1323_, 1);
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
    mut v_m_1344_: *mut LeanObject,
    mut v_a_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1346_: *mut LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_1344_, v_a_1345_);
    lean_dec_ref(v_a_1345_);
    lean_dec_ref(v_m_1344_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(
    mut v_x_1347_: *mut LeanObject,
    mut v_t_1348_: *mut LeanObject,
    mut v_v_1349_: *mut LeanObject,
    mut v_b_1350_: *mut LeanObject,
    mut v_nondep_1351_: u8,
    mut v___y_1352_: *mut LeanObject,
    mut v___y_1353_: u8,
    mut v___y_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1375_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_1348_);
                    v___x_1370_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1348_,
                        v___y_1353_,
                        v___y_1354_,
                    );
                    v_snd_1371_ = lean_ctor_get(v___x_1370_, 1);
                    lean_inc(v_snd_1371_);
                    lean_dec_ref(v___x_1370_);
                    lean_inc_ref(v_v_1349_);
                    v___x_1372_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_1349_,
                        v___y_1353_,
                        v_snd_1371_,
                    );
                    v_snd_1373_ = lean_ctor_get(v___x_1372_, 1);
                    lean_inc(v_snd_1373_);
                    lean_dec_ref(v___x_1372_);
                    lean_inc_ref(v_b_1350_);
                    v___x_1374_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1350_,
                        v___y_1353_,
                        v_snd_1373_,
                    );
                    v_snd_1375_ = lean_ctor_get(v___x_1374_, 1);
                    lean_inc(v_snd_1375_);
                    lean_dec_ref(v___x_1374_);
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
                v_fst_1360_ = lean_ctor_get(v___x_1359_, 0);
                v_snd_1361_ = lean_ctor_get(v___x_1359_, 1);
                v_isSharedCheck_1369_ = (!lean_is_exclusive(v___x_1359_)) as u8;
                if v_isSharedCheck_1369_ == 0 {
                    v___x_1363_ = v___x_1359_;
                    v_isShared_1364_ = v_isSharedCheck_1369_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1361_);
                    lean_inc(v_fst_1360_);
                    lean_dec(v___x_1359_);
                    v___x_1363_ = lean_box(0);
                    v_isShared_1364_ = v_isSharedCheck_1369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1364_ == 0 {
                    lean_ctor_set(v___x_1363_, 1, v___y_1356_);
                    v___x_1366_ = v___x_1363_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1360_);
                    lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___y_1356_);
                    v___x_1366_ = v_reuseFailAlloc_1368_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1367_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1367_, 0, v___x_1366_);
                lean_ctor_set(v___x_1367_, 1, v_snd_1361_);
                return v___x_1367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(
    mut v_x_1376_: *mut LeanObject,
    mut v_t_1377_: *mut LeanObject,
    mut v_v_1378_: *mut LeanObject,
    mut v_b_1379_: *mut LeanObject,
    mut v_nondep_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_1384_: u8 = 0;
    let mut v___y_21403__boxed_1385_: u8 = 0;
    let mut v_res_1386_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_1384_ = (lean_unbox(v_nondep_1380_) as u8);
    v___y_21403__boxed_1385_ = (lean_unbox(v___y_1382_) as u8);
    v_res_1386_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_1376_, v_t_1377_, v_v_1378_, v_b_1379_, v_nondep_boxed_1384_, v___y_1381_, v___y_21403__boxed_1385_, v___y_1383_);
    return v_res_1386_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(
    mut v_d_1387_: *mut LeanObject,
    mut v_e_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: u8,
    mut v___y_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1408_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_e_1388_);
                    v___x_1407_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_1388_,
                        v___y_1390_,
                        v___y_1391_,
                    );
                    v_snd_1408_ = lean_ctor_get(v___x_1407_, 1);
                    lean_inc(v_snd_1408_);
                    lean_dec_ref(v___x_1407_);
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
                v_fst_1397_ = lean_ctor_get(v___x_1396_, 0);
                v_snd_1398_ = lean_ctor_get(v___x_1396_, 1);
                v_isSharedCheck_1406_ = (!lean_is_exclusive(v___x_1396_)) as u8;
                if v_isSharedCheck_1406_ == 0 {
                    v___x_1400_ = v___x_1396_;
                    v_isShared_1401_ = v_isSharedCheck_1406_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1398_);
                    lean_inc(v_fst_1397_);
                    lean_dec(v___x_1396_);
                    v___x_1400_ = lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1401_ == 0 {
                    lean_ctor_set(v___x_1400_, 1, v___y_1393_);
                    v___x_1403_ = v___x_1400_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_fst_1397_);
                    lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___y_1393_);
                    v___x_1403_ = v_reuseFailAlloc_1405_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1404_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1404_, 0, v___x_1403_);
                lean_ctor_set(v___x_1404_, 1, v_snd_1398_);
                return v___x_1404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(
    mut v_d_1409_: *mut LeanObject,
    mut v_e_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21457__boxed_1414_: u8 = 0;
    let mut v_res_1415_: *mut LeanObject = core::ptr::null_mut();
    v___y_21457__boxed_1414_ = (lean_unbox(v___y_1412_) as u8);
    v_res_1415_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_1409_, v_e_1410_, v___y_1411_, v___y_21457__boxed_1414_, v___y_1413_);
    return v_res_1415_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2;
    v___x_1420_ = lean_unsigned_to_nat(67);
    v___x_1421_ = lean_unsigned_to_nat(35);
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
    mut v_s_1425_: *mut LeanObject,
    mut v_d_1426_: *mut LeanObject,
    mut v_e_1427_: *mut LeanObject,
    mut v_offset_1428_: *mut LeanObject,
    mut v_a_1429_: *mut LeanObject,
    mut v_a_1430_: u8,
    mut v_a_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v_fst_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___y_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_binderName_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1466_: u8 = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v_fst_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___y_1486_: u8 = 0;
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1495_: u8 = 0;
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v_binderName_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1501_: u8 = 0;
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v_fst_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___y_1521_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: u8 = 0;
    let mut v___x_1530_: u8 = 0;
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_isSharedCheck_1532_: u8 = 0;
    let mut v_declName_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1537_: u8 = 0;
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_fst_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___y_1562_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: u8 = 0;
    let mut v___x_1573_: u8 = 0;
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut v_data_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v_fst_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_typeName_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v_fst_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_1427_) {
                5 => {
                    v_fn_1432_ = lean_ctor_get(v_e_1427_, 0);
                    v_arg_1433_ = lean_ctor_get(v_e_1427_, 1);
                    lean_inc(v_offset_1428_);
                    lean_inc_ref(v_fn_1432_);
                    v___x_1434_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_fn_1432_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1435_ = lean_ctor_get(v___x_1434_, 0);
                    lean_inc(v_fst_1435_);
                    v_snd_1436_ = lean_ctor_get(v___x_1434_, 1);
                    lean_inc(v_snd_1436_);
                    lean_dec_ref(v___x_1434_);
                    v_fst_1437_ = lean_ctor_get(v_fst_1435_, 0);
                    lean_inc(v_fst_1437_);
                    v_snd_1438_ = lean_ctor_get(v_fst_1435_, 1);
                    lean_inc(v_snd_1438_);
                    lean_dec(v_fst_1435_);
                    lean_inc_ref(v_arg_1433_);
                    v___x_1439_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_arg_1433_, v_offset_1428_, v_snd_1438_, v_a_1430_, v_snd_1436_);
                    v_fst_1440_ = lean_ctor_get(v___x_1439_, 0);
                    v_snd_1441_ = lean_ctor_get(v___x_1439_, 1);
                    v_isSharedCheck_1462_ = (!lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1443_ = v___x_1439_;
                        v_isShared_1444_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1441_);
                        lean_inc(v_fst_1440_);
                        lean_dec(v___x_1439_);
                        v___x_1443_ = lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_1463_ = lean_ctor_get(v_e_1427_, 0);
                    v_binderType_1464_ = lean_ctor_get(v_e_1427_, 1);
                    v_body_1465_ = lean_ctor_get(v_e_1427_, 2);
                    v_binderInfo_1466_ = lean_ctor_get_uint8(
                        v_e_1427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_1428_);
                    lean_inc_ref(v_binderType_1464_);
                    v___x_1467_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_binderType_1464_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1468_ = lean_ctor_get(v___x_1467_, 0);
                    lean_inc(v_fst_1468_);
                    v_snd_1469_ = lean_ctor_get(v___x_1467_, 1);
                    lean_inc(v_snd_1469_);
                    lean_dec_ref(v___x_1467_);
                    v_fst_1470_ = lean_ctor_get(v_fst_1468_, 0);
                    lean_inc(v_fst_1470_);
                    v_snd_1471_ = lean_ctor_get(v_fst_1468_, 1);
                    lean_inc(v_snd_1471_);
                    lean_dec(v_fst_1468_);
                    v___x_1472_ = lean_unsigned_to_nat(1);
                    v___x_1473_ = lean_nat_add(v_offset_1428_, v___x_1472_);
                    lean_dec(v_offset_1428_);
                    lean_inc_ref(v_body_1465_);
                    v___x_1474_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_body_1465_, v___x_1473_, v_snd_1471_, v_a_1430_, v_snd_1469_);
                    v_fst_1475_ = lean_ctor_get(v___x_1474_, 0);
                    v_snd_1476_ = lean_ctor_get(v___x_1474_, 1);
                    v_isSharedCheck_1497_ = (!lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1478_ = v___x_1474_;
                        v_isShared_1479_ = v_isSharedCheck_1497_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_1476_);
                        lean_inc(v_fst_1475_);
                        lean_dec(v___x_1474_);
                        v___x_1478_ = lean_box(0);
                        v_isShared_1479_ = v_isSharedCheck_1497_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_1498_ = lean_ctor_get(v_e_1427_, 0);
                    v_binderType_1499_ = lean_ctor_get(v_e_1427_, 1);
                    v_body_1500_ = lean_ctor_get(v_e_1427_, 2);
                    v_binderInfo_1501_ = lean_ctor_get_uint8(
                        v_e_1427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_1428_);
                    lean_inc_ref(v_binderType_1499_);
                    v___x_1502_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_binderType_1499_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1503_ = lean_ctor_get(v___x_1502_, 0);
                    lean_inc(v_fst_1503_);
                    v_snd_1504_ = lean_ctor_get(v___x_1502_, 1);
                    lean_inc(v_snd_1504_);
                    lean_dec_ref(v___x_1502_);
                    v_fst_1505_ = lean_ctor_get(v_fst_1503_, 0);
                    lean_inc(v_fst_1505_);
                    v_snd_1506_ = lean_ctor_get(v_fst_1503_, 1);
                    lean_inc(v_snd_1506_);
                    lean_dec(v_fst_1503_);
                    v___x_1507_ = lean_unsigned_to_nat(1);
                    v___x_1508_ = lean_nat_add(v_offset_1428_, v___x_1507_);
                    lean_dec(v_offset_1428_);
                    lean_inc_ref(v_body_1500_);
                    v___x_1509_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_body_1500_, v___x_1508_, v_snd_1506_, v_a_1430_, v_snd_1504_);
                    v_fst_1510_ = lean_ctor_get(v___x_1509_, 0);
                    v_snd_1511_ = lean_ctor_get(v___x_1509_, 1);
                    v_isSharedCheck_1532_ = (!lean_is_exclusive(v___x_1509_)) as u8;
                    if v_isSharedCheck_1532_ == 0 {
                        v___x_1513_ = v___x_1509_;
                        v_isShared_1514_ = v_isSharedCheck_1532_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_1511_);
                        lean_inc(v_fst_1510_);
                        lean_dec(v___x_1509_);
                        v___x_1513_ = lean_box(0);
                        v_isShared_1514_ = v_isSharedCheck_1532_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_1533_ = lean_ctor_get(v_e_1427_, 0);
                    v_type_1534_ = lean_ctor_get(v_e_1427_, 1);
                    v_value_1535_ = lean_ctor_get(v_e_1427_, 2);
                    v_body_1536_ = lean_ctor_get(v_e_1427_, 3);
                    v_nondep_1537_ = lean_ctor_get_uint8(
                        v_e_1427_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_n(v_offset_1428_, 2);
                    lean_inc_ref(v_type_1534_);
                    v___x_1538_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_type_1534_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1539_ = lean_ctor_get(v___x_1538_, 0);
                    lean_inc(v_fst_1539_);
                    v_snd_1540_ = lean_ctor_get(v___x_1538_, 1);
                    lean_inc(v_snd_1540_);
                    lean_dec_ref(v___x_1538_);
                    v_fst_1541_ = lean_ctor_get(v_fst_1539_, 0);
                    lean_inc(v_fst_1541_);
                    v_snd_1542_ = lean_ctor_get(v_fst_1539_, 1);
                    lean_inc(v_snd_1542_);
                    lean_dec(v_fst_1539_);
                    lean_inc_ref(v_value_1535_);
                    v___x_1543_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_value_1535_, v_offset_1428_, v_snd_1542_, v_a_1430_, v_snd_1540_);
                    v_fst_1544_ = lean_ctor_get(v___x_1543_, 0);
                    lean_inc(v_fst_1544_);
                    v_snd_1545_ = lean_ctor_get(v___x_1543_, 1);
                    lean_inc(v_snd_1545_);
                    lean_dec_ref(v___x_1543_);
                    v_fst_1546_ = lean_ctor_get(v_fst_1544_, 0);
                    lean_inc(v_fst_1546_);
                    v_snd_1547_ = lean_ctor_get(v_fst_1544_, 1);
                    lean_inc(v_snd_1547_);
                    lean_dec(v_fst_1544_);
                    v___x_1548_ = lean_unsigned_to_nat(1);
                    v___x_1549_ = lean_nat_add(v_offset_1428_, v___x_1548_);
                    lean_dec(v_offset_1428_);
                    lean_inc_ref(v_body_1536_);
                    v___x_1550_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_body_1536_, v___x_1549_, v_snd_1547_, v_a_1430_, v_snd_1545_);
                    v_fst_1551_ = lean_ctor_get(v___x_1550_, 0);
                    v_snd_1552_ = lean_ctor_get(v___x_1550_, 1);
                    v_isSharedCheck_1575_ = (!lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1575_ == 0 {
                        v___x_1554_ = v___x_1550_;
                        v_isShared_1555_ = v_isSharedCheck_1575_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_snd_1552_);
                        lean_inc(v_fst_1551_);
                        lean_dec(v___x_1550_);
                        v___x_1554_ = lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1575_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_1576_ = lean_ctor_get(v_e_1427_, 0);
                    v_expr_1577_ = lean_ctor_get(v_e_1427_, 1);
                    lean_inc_ref(v_expr_1577_);
                    v___x_1578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_expr_1577_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1579_ = lean_ctor_get(v___x_1578_, 0);
                    v_snd_1580_ = lean_ctor_get(v___x_1578_, 1);
                    v_isSharedCheck_1598_ = (!lean_is_exclusive(v___x_1578_)) as u8;
                    if v_isSharedCheck_1598_ == 0 {
                        v___x_1582_ = v___x_1578_;
                        v_isShared_1583_ = v_isSharedCheck_1598_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_snd_1580_);
                        lean_inc(v_fst_1579_);
                        lean_dec(v___x_1578_);
                        v___x_1582_ = lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1598_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_1599_ = lean_ctor_get(v_e_1427_, 0);
                    v_idx_1600_ = lean_ctor_get(v_e_1427_, 1);
                    v_struct_1601_ = lean_ctor_get(v_e_1427_, 2);
                    lean_inc_ref(v_struct_1601_);
                    v___x_1602_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1425_, v_d_1426_, v_struct_1601_, v_offset_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
                    v_fst_1603_ = lean_ctor_get(v___x_1602_, 0);
                    v_snd_1604_ = lean_ctor_get(v___x_1602_, 1);
                    v_isSharedCheck_1622_ = (!lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1622_ == 0 {
                        v___x_1606_ = v___x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1622_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_snd_1604_);
                        lean_inc(v_fst_1603_);
                        lean_dec(v___x_1602_);
                        v___x_1606_ = lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1622_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_offset_1428_);
                    lean_dec_ref(v_e_1427_);
                    v___x_1623_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
                    v___x_1624_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_1623_, v_a_1429_, v_a_1430_, v_a_1431_);
                    return v___x_1624_;
                }
            },
            1 => {
                v_fst_1445_ = lean_ctor_get(v_fst_1440_, 0);
                v_snd_1446_ = lean_ctor_get(v_fst_1440_, 1);
                v_isSharedCheck_1461_ = (!lean_is_exclusive(v_fst_1440_)) as u8;
                if v_isSharedCheck_1461_ == 0 {
                    v___x_1448_ = v_fst_1440_;
                    v_isShared_1449_ = v_isSharedCheck_1461_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1446_);
                    lean_inc(v_fst_1445_);
                    lean_dec(v_fst_1440_);
                    v___x_1448_ = lean_box(0);
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
                    lean_del_object(v___x_1448_);
                    lean_del_object(v___x_1443_);
                    lean_dec_ref_known(v_e_1427_, 2);
                    v___x_1452_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_1437_, v_fst_1445_, v_snd_1446_, v_a_1430_, v_snd_1441_);
                    return v___x_1452_;
                } else {
                    lean_dec(v_fst_1445_);
                    lean_dec(v_fst_1437_);
                    if v_isShared_1449_ == 0 {
                        lean_ctor_set(v___x_1448_, 0, v_e_1427_);
                        v___x_1454_ = v___x_1448_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_e_1427_);
                        lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_snd_1446_);
                        v___x_1454_ = v_reuseFailAlloc_1458_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1444_ == 0 {
                    lean_ctor_set(v___x_1443_, 0, v___x_1454_);
                    v___x_1456_ = v___x_1443_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_snd_1441_);
                    v___x_1456_ = v_reuseFailAlloc_1457_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1456_;
            }
            6 => {
                v_fst_1480_ = lean_ctor_get(v_fst_1475_, 0);
                v_snd_1481_ = lean_ctor_get(v_fst_1475_, 1);
                v_isSharedCheck_1496_ = (!lean_is_exclusive(v_fst_1475_)) as u8;
                if v_isSharedCheck_1496_ == 0 {
                    v___x_1483_ = v_fst_1475_;
                    v_isShared_1484_ = v_isSharedCheck_1496_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_1481_);
                    lean_inc(v_fst_1480_);
                    lean_dec(v_fst_1475_);
                    v___x_1483_ = lean_box(0);
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
                    lean_inc(v_binderName_1463_);
                    lean_del_object(v___x_1483_);
                    lean_del_object(v___x_1478_);
                    lean_dec_ref_known(v_e_1427_, 3);
                    v___x_1487_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_1463_, v_binderInfo_1466_, v_fst_1470_, v_fst_1480_, v_snd_1481_, v_a_1430_, v_snd_1476_);
                    return v___x_1487_;
                } else {
                    lean_dec(v_fst_1480_);
                    lean_dec(v_fst_1470_);
                    if v_isShared_1484_ == 0 {
                        lean_ctor_set(v___x_1483_, 0, v_e_1427_);
                        v___x_1489_ = v___x_1483_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_e_1427_);
                        lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_snd_1481_);
                        v___x_1489_ = v_reuseFailAlloc_1493_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1479_ == 0 {
                    lean_ctor_set(v___x_1478_, 0, v___x_1489_);
                    v___x_1491_ = v___x_1478_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
                    lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1476_);
                    v___x_1491_ = v_reuseFailAlloc_1492_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1491_;
            }
            11 => {
                v_fst_1515_ = lean_ctor_get(v_fst_1510_, 0);
                v_snd_1516_ = lean_ctor_get(v_fst_1510_, 1);
                v_isSharedCheck_1531_ = (!lean_is_exclusive(v_fst_1510_)) as u8;
                if v_isSharedCheck_1531_ == 0 {
                    v___x_1518_ = v_fst_1510_;
                    v_isShared_1519_ = v_isSharedCheck_1531_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_1516_);
                    lean_inc(v_fst_1515_);
                    lean_dec(v_fst_1510_);
                    v___x_1518_ = lean_box(0);
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
                    lean_inc(v_binderName_1498_);
                    lean_del_object(v___x_1518_);
                    lean_del_object(v___x_1513_);
                    lean_dec_ref_known(v_e_1427_, 3);
                    v___x_1522_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1498_, v_binderInfo_1501_, v_fst_1505_, v_fst_1515_, v_snd_1516_, v_a_1430_, v_snd_1511_);
                    return v___x_1522_;
                } else {
                    lean_dec(v_fst_1515_);
                    lean_dec(v_fst_1505_);
                    if v_isShared_1519_ == 0 {
                        lean_ctor_set(v___x_1518_, 0, v_e_1427_);
                        v___x_1524_ = v___x_1518_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_e_1427_);
                        lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_snd_1516_);
                        v___x_1524_ = v_reuseFailAlloc_1528_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1514_ == 0 {
                    lean_ctor_set(v___x_1513_, 0, v___x_1524_);
                    v___x_1526_ = v___x_1513_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_snd_1511_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1526_;
            }
            16 => {
                v_fst_1556_ = lean_ctor_get(v_fst_1551_, 0);
                v_snd_1557_ = lean_ctor_get(v_fst_1551_, 1);
                v_isSharedCheck_1574_ = (!lean_is_exclusive(v_fst_1551_)) as u8;
                if v_isSharedCheck_1574_ == 0 {
                    v___x_1559_ = v_fst_1551_;
                    v_isShared_1560_ = v_isSharedCheck_1574_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_1557_);
                    lean_inc(v_fst_1556_);
                    lean_dec(v_fst_1551_);
                    v___x_1559_ = lean_box(0);
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
                    lean_inc(v_declName_1533_);
                    lean_del_object(v___x_1559_);
                    lean_del_object(v___x_1554_);
                    lean_dec_ref_known(v_e_1427_, 4);
                    v___x_1563_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1533_, v_fst_1541_, v_fst_1546_, v_fst_1556_, v_nondep_1537_, v_snd_1557_, v_a_1430_, v_snd_1552_);
                    return v___x_1563_;
                } else {
                    v___x_1564_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1536_,
                            v_fst_1556_,
                        );
                    if v___x_1564_ == 0 {
                        lean_inc(v_declName_1533_);
                        lean_del_object(v___x_1559_);
                        lean_del_object(v___x_1554_);
                        lean_dec_ref_known(v_e_1427_, 4);
                        v___x_1565_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1533_, v_fst_1541_, v_fst_1546_, v_fst_1556_, v_nondep_1537_, v_snd_1557_, v_a_1430_, v_snd_1552_);
                        return v___x_1565_;
                    } else {
                        lean_dec(v_fst_1556_);
                        lean_dec(v_fst_1546_);
                        lean_dec(v_fst_1541_);
                        if v_isShared_1560_ == 0 {
                            lean_ctor_set(v___x_1559_, 0, v_e_1427_);
                            v___x_1567_ = v___x_1559_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_e_1427_);
                            lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_snd_1557_);
                            v___x_1567_ = v_reuseFailAlloc_1571_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1555_ == 0 {
                    lean_ctor_set(v___x_1554_, 0, v___x_1567_);
                    v___x_1569_ = v___x_1554_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1552_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1569_;
            }
            21 => {
                v_fst_1584_ = lean_ctor_get(v_fst_1579_, 0);
                v_snd_1585_ = lean_ctor_get(v_fst_1579_, 1);
                v_isSharedCheck_1597_ = (!lean_is_exclusive(v_fst_1579_)) as u8;
                if v_isSharedCheck_1597_ == 0 {
                    v___x_1587_ = v_fst_1579_;
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_1585_);
                    lean_inc(v_fst_1584_);
                    lean_dec(v_fst_1579_);
                    v___x_1587_ = lean_box(0);
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
                    lean_inc(v_data_1576_);
                    lean_del_object(v___x_1587_);
                    lean_del_object(v___x_1582_);
                    lean_dec_ref_known(v_e_1427_, 2);
                    v___x_1590_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1576_, v_fst_1584_, v_snd_1585_, v_a_1430_, v_snd_1580_);
                    return v___x_1590_;
                } else {
                    lean_dec(v_fst_1584_);
                    if v_isShared_1588_ == 0 {
                        lean_ctor_set(v___x_1587_, 0, v_e_1427_);
                        v___x_1592_ = v___x_1587_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_e_1427_);
                        lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_snd_1585_);
                        v___x_1592_ = v_reuseFailAlloc_1596_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1583_ == 0 {
                    lean_ctor_set(v___x_1582_, 0, v___x_1592_);
                    v___x_1594_ = v___x_1582_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
                    lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_snd_1580_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1594_;
            }
            25 => {
                v_fst_1608_ = lean_ctor_get(v_fst_1603_, 0);
                v_snd_1609_ = lean_ctor_get(v_fst_1603_, 1);
                v_isSharedCheck_1621_ = (!lean_is_exclusive(v_fst_1603_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v___x_1611_ = v_fst_1603_;
                    v_isShared_1612_ = v_isSharedCheck_1621_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_1609_);
                    lean_inc(v_fst_1608_);
                    lean_dec(v_fst_1603_);
                    v___x_1611_ = lean_box(0);
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
                    lean_inc(v_idx_1600_);
                    lean_inc(v_typeName_1599_);
                    lean_del_object(v___x_1611_);
                    lean_del_object(v___x_1606_);
                    lean_dec_ref_known(v_e_1427_, 3);
                    v___x_1614_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_1599_, v_idx_1600_, v_fst_1608_, v_snd_1609_, v_a_1430_, v_snd_1604_);
                    return v___x_1614_;
                } else {
                    lean_dec(v_fst_1608_);
                    if v_isShared_1612_ == 0 {
                        lean_ctor_set(v___x_1611_, 0, v_e_1427_);
                        v___x_1616_ = v___x_1611_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_e_1427_);
                        lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_snd_1609_);
                        v___x_1616_ = v_reuseFailAlloc_1620_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_1607_ == 0 {
                    lean_ctor_set(v___x_1606_, 0, v___x_1616_);
                    v___x_1618_ = v___x_1606_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_snd_1604_);
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
    mut v_s_1625_: *mut LeanObject,
    mut v_d_1626_: *mut LeanObject,
    mut v_e_1627_: *mut LeanObject,
    mut v_offset_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
    mut v_a_1630_: u8,
    mut v_a_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_u2081_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    let mut v_deBruijnIndex_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_offset_1628_);
                lean_inc_ref(v_e_1627_);
                v_key_1632_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_key_1632_, 0, v_e_1627_);
                lean_ctor_set(v_key_1632_, 1, v_offset_1628_);
                v___x_1647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_1629_, v_key_1632_);
                if lean_obj_tag(v___x_1647_) == 1 {
                    lean_dec_ref_known(v_key_1632_, 2);
                    lean_dec(v_offset_1628_);
                    lean_dec_ref(v_e_1627_);
                    v_val_1648_ = lean_ctor_get(v___x_1647_, 0);
                    lean_inc(v_val_1648_);
                    lean_dec_ref_known(v___x_1647_, 1);
                    v___x_1649_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1649_, 0, v_val_1648_);
                    lean_ctor_set(v___x_1649_, 1, v_a_1629_);
                    v___x_1650_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1650_, 0, v___x_1649_);
                    lean_ctor_set(v___x_1650_, 1, v_a_1631_);
                    return v___x_1650_;
                } else {
                    lean_dec(v___x_1647_);
                    v_s_u2081_1651_ = lean_nat_add(v_s_1625_, v_offset_1628_);
                    v___x_1652_ = l_Lean_Expr_looseBVarRange(v_e_1627_);
                    v___x_1653_ = lean_nat_dec_le(v___x_1652_, v_s_u2081_1651_);
                    lean_dec(v___x_1652_);
                    if v___x_1653_ == 0 {
                        if lean_obj_tag(v_e_1627_) == 0 {
                            v_deBruijnIndex_1654_ = lean_ctor_get(v_e_1627_, 0);
                            v___x_1655_ = lean_nat_dec_le(v_s_u2081_1651_, v_deBruijnIndex_1654_);
                            lean_dec(v_s_u2081_1651_);
                            if v___x_1655_ == 0 {
                                v_snd_1634_ = v_a_1631_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_deBruijnIndex_1654_);
                                lean_dec_ref_known(v_e_1627_, 1);
                                lean_dec(v_offset_1628_);
                                v___x_1656_ = lean_nat_sub(v_deBruijnIndex_1654_, v_d_1626_);
                                lean_dec(v_deBruijnIndex_1654_);
                                v___x_1657_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1656_, v_a_1631_);
                                v_fst_1658_ = lean_ctor_get(v___x_1657_, 0);
                                lean_inc(v_fst_1658_);
                                v_snd_1659_ = lean_ctor_get(v___x_1657_, 1);
                                lean_inc(v_snd_1659_);
                                lean_dec_ref(v___x_1657_);
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
                            lean_dec(v_s_u2081_1651_);
                            v_snd_1634_ = v_a_1631_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_s_u2081_1651_);
                        lean_dec(v_offset_1628_);
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
            1 => match lean_obj_tag(v_e_1627_) {
                9 => {
                    lean_dec(v_offset_1628_);
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
                    lean_dec(v_offset_1628_);
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
                    lean_dec(v_offset_1628_);
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
                    lean_dec(v_offset_1628_);
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
                    lean_dec(v_offset_1628_);
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
                    lean_dec(v_offset_1628_);
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
                    v_fst_1642_ = lean_ctor_get(v___x_1641_, 0);
                    lean_inc(v_fst_1642_);
                    v_snd_1643_ = lean_ctor_get(v___x_1641_, 1);
                    lean_inc(v_snd_1643_);
                    lean_dec_ref(v___x_1641_);
                    v_fst_1644_ = lean_ctor_get(v_fst_1642_, 0);
                    lean_inc(v_fst_1644_);
                    v_snd_1645_ = lean_ctor_get(v_fst_1642_, 1);
                    lean_inc(v_snd_1645_);
                    lean_dec(v_fst_1642_);
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
    mut v_s_1662_: *mut LeanObject,
    mut v_d_1663_: *mut LeanObject,
    mut v_e_1664_: *mut LeanObject,
    mut v_offset_1665_: *mut LeanObject,
    mut v_a_1666_: *mut LeanObject,
    mut v_a_1667_: *mut LeanObject,
    mut v_a_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1669_: u8 = 0;
    let mut v_res_1670_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1669_ = (lean_unbox(v_a_1667_) as u8);
    v_res_1670_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_1662_, v_d_1663_, v_e_1664_, v_offset_1665_, v_a_1666_, v_a_boxed_1669_, v_a_1668_);
    lean_dec(v_d_1663_);
    lean_dec(v_s_1662_);
    return v_res_1670_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(
    mut v_s_1671_: *mut LeanObject,
    mut v_d_1672_: *mut LeanObject,
    mut v_e_1673_: *mut LeanObject,
    mut v_offset_1674_: *mut LeanObject,
    mut v_a_1675_: *mut LeanObject,
    mut v_a_1676_: *mut LeanObject,
    mut v_a_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1678_: u8 = 0;
    let mut v_res_1679_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1678_ = (lean_unbox(v_a_1676_) as u8);
    v_res_1679_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_1671_, v_d_1672_, v_e_1673_, v_offset_1674_, v_a_1675_, v_a_boxed_1678_, v_a_1677_);
    lean_dec(v_d_1672_);
    lean_dec(v_s_1671_);
    return v_res_1679_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0() -> *mut LeanObject {
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1680_ = lean_box(0);
    v___x_1681_ = lean_unsigned_to_nat(16);
    v___x_1682_ = lean_mk_array(v___x_1681_, v___x_1680_);
    return v___x_1682_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1() -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once),
        _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0,
    );
    v___x_1684_ = lean_unsigned_to_nat(0);
    v___x_1685_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1685_, 0, v___x_1684_);
    lean_ctor_set(v___x_1685_, 1, v___x_1683_);
    return v___x_1685_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS_x27(
    mut v_e_1686_: *mut LeanObject,
    mut v_s_1687_: *mut LeanObject,
    mut v_d_1688_: *mut LeanObject,
    mut v_a_1689_: u8,
    mut v_a_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_unused_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1691_ = l_Lean_Expr_looseBVarRange(v_e_1686_);
                v___x_1692_ = lean_nat_dec_le(v___x_1691_, v_s_1687_);
                lean_dec(v___x_1691_);
                if v___x_1692_ == 0 {
                    v___x_1693_ = lean_unsigned_to_nat(0);
                    if lean_obj_tag(v_e_1686_) == 0 {
                        v_deBruijnIndex_1715_ = lean_ctor_get(v_e_1686_, 0);
                        v___x_1716_ = lean_nat_dec_le(v_s_1687_, v_deBruijnIndex_1715_);
                        if v___x_1716_ == 0 {
                            v_snd_1695_ = v_a_1690_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_deBruijnIndex_1715_);
                            lean_dec_ref_known(v_e_1686_, 1);
                            v___x_1717_ = lean_nat_sub(v_deBruijnIndex_1715_, v_d_1688_);
                            lean_dec(v_deBruijnIndex_1715_);
                            v___x_1718_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1717_, v_a_1690_);
                            return v___x_1718_;
                        }
                    } else {
                        v_snd_1695_ = v_a_1690_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1719_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1719_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1719_, 1, v_a_1690_);
                    return v___x_1719_;
                }
            }
            1 => match lean_obj_tag(v_e_1686_) {
                9 => {
                    v___x_1696_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1696_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1696_, 1, v_snd_1695_);
                    return v___x_1696_;
                }
                2 => {
                    v___x_1697_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1697_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1697_, 1, v_snd_1695_);
                    return v___x_1697_;
                }
                0 => {
                    v___x_1698_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1698_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1698_, 1, v_snd_1695_);
                    return v___x_1698_;
                }
                1 => {
                    v___x_1699_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1699_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1699_, 1, v_snd_1695_);
                    return v___x_1699_;
                }
                4 => {
                    v___x_1700_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1700_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1700_, 1, v_snd_1695_);
                    return v___x_1700_;
                }
                3 => {
                    v___x_1701_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1701_, 0, v_e_1686_);
                    lean_ctor_set(v___x_1701_, 1, v_snd_1695_);
                    return v___x_1701_;
                }
                _ => {
                    v___x_1702_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1,
                    );
                    v___x_1703_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_1687_, v_d_1688_, v_e_1686_, v___x_1693_, v___x_1702_, v_a_1689_, v_snd_1695_);
                    v_fst_1704_ = lean_ctor_get(v___x_1703_, 0);
                    lean_inc(v_fst_1704_);
                    v_snd_1705_ = lean_ctor_get(v___x_1703_, 1);
                    lean_inc(v_snd_1705_);
                    lean_dec_ref(v___x_1703_);
                    v_fst_1706_ = lean_ctor_get(v_fst_1704_, 0);
                    v_isSharedCheck_1713_ = (!lean_is_exclusive(v_fst_1704_)) as u8;
                    if v_isSharedCheck_1713_ == 0 {
                        v_unused_1714_ = lean_ctor_get(v_fst_1704_, 1);
                        lean_dec(v_unused_1714_);
                        v___x_1708_ = v_fst_1704_;
                        v_isShared_1709_ = v_isSharedCheck_1713_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_1706_);
                        lean_dec(v_fst_1704_);
                        v___x_1708_ = lean_box(0);
                        v_isShared_1709_ = v_isSharedCheck_1713_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => {
                if v_isShared_1709_ == 0 {
                    lean_ctor_set(v___x_1708_, 1, v_snd_1705_);
                    v___x_1711_ = v___x_1708_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_fst_1706_);
                    lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_snd_1705_);
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
    mut v_e_1720_: *mut LeanObject,
    mut v_s_1721_: *mut LeanObject,
    mut v_d_1722_: *mut LeanObject,
    mut v_a_1723_: *mut LeanObject,
    mut v_a_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1725_: u8 = 0;
    let mut v_res_1726_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1725_ = (lean_unbox(v_a_1723_) as u8);
    v_res_1726_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(
        v_e_1720_,
        v_s_1721_,
        v_d_1722_,
        v_a_boxed_1725_,
        v_a_1724_,
    );
    lean_dec(v_d_1722_);
    lean_dec(v_s_1721_);
    return v_res_1726_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1727_: *mut LeanObject,
    mut v_m_1728_: *mut LeanObject,
    mut v_a_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_1728_, v_a_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_1731_: *mut LeanObject,
    mut v_m_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1734_: *mut LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_1731_, v_m_1732_, v_a_1733_);
    lean_dec_ref(v_a_1733_);
    lean_dec_ref(v_m_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(
    mut v_00_u03b2_1735_: *mut LeanObject,
    mut v_a_1736_: *mut LeanObject,
    mut v_x_1737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    v___x_1738_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_1736_, v_x_1737_);
    return v___x_1738_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(
    mut v_00_u03b2_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_x_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1742_: *mut LeanObject = core::ptr::null_mut();
    v_res_1742_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_1739_, v_a_1740_, v_x_1741_);
    lean_dec(v_x_1741_);
    lean_dec_ref(v_a_1740_);
    return v_res_1742_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1743_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    v___x_1744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
    v___x_1745_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(
    mut v_00_u03b2_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    v___x_1747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1);
    return v___x_1747_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_box(0));
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(
    mut v_e_1749_: *mut LeanObject,
    mut v_s_1750_: *mut LeanObject,
    mut v_d_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1765_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1774_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut v_unused_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1754_ = lean_st_ref_take(v_a_1752_);
                v_share_1755_ = lean_ctor_get(v___x_1754_, 0);
                v_maxFVar_1756_ = lean_ctor_get(v___x_1754_, 1);
                v_proofInstInfo_1757_ = lean_ctor_get(v___x_1754_, 2);
                v_inferType_1758_ = lean_ctor_get(v___x_1754_, 3);
                v_getLevel_1759_ = lean_ctor_get(v___x_1754_, 4);
                v_congrInfo_1760_ = lean_ctor_get(v___x_1754_, 5);
                v_defEqI_1761_ = lean_ctor_get(v___x_1754_, 6);
                v_extensions_1762_ = lean_ctor_get(v___x_1754_, 7);
                v_issues_1763_ = lean_ctor_get(v___x_1754_, 8);
                v_canon_1764_ = lean_ctor_get(v___x_1754_, 9);
                v_debug_1765_ = lean_ctor_get_uint8(
                    v___x_1754_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1800_ = (!lean_is_exclusive(v___x_1754_)) as u8;
                if v_isSharedCheck_1800_ == 0 {
                    v___x_1767_ = v___x_1754_;
                    v_isShared_1768_ = v_isSharedCheck_1800_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_1764_);
                    lean_inc(v_issues_1763_);
                    lean_inc(v_extensions_1762_);
                    lean_inc(v_defEqI_1761_);
                    lean_inc(v_congrInfo_1760_);
                    lean_inc(v_getLevel_1759_);
                    lean_inc(v_inferType_1758_);
                    lean_inc(v_proofInstInfo_1757_);
                    lean_inc(v_maxFVar_1756_);
                    lean_inc(v_share_1755_);
                    lean_dec(v___x_1754_);
                    v___x_1767_ = lean_box(0);
                    v_isShared_1768_ = v_isSharedCheck_1800_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1769_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0,
                );
                if v_isShared_1768_ == 0 {
                    lean_ctor_set(v___x_1767_, 0, v___x_1769_);
                    v___x_1771_ = v___x_1767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_maxFVar_1756_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_proofInstInfo_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_inferType_1758_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_getLevel_1759_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_congrInfo_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_defEqI_1761_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_extensions_1762_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_issues_1763_);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 9, v_canon_1764_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1799_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_1774_ = lean_ctor_get_uint8(
                    v___x_1773_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_1773_);
                v___x_1775_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(
                    v_e_1749_,
                    v_s_1750_,
                    v_d_1751_,
                    v_debug_1774_,
                    v_share_1755_,
                );
                v_fst_1776_ = lean_ctor_get(v___x_1775_, 0);
                lean_inc(v_fst_1776_);
                v_snd_1777_ = lean_ctor_get(v___x_1775_, 1);
                lean_inc(v_snd_1777_);
                lean_dec_ref(v___x_1775_);
                v___x_1778_ = lean_st_ref_take(v_a_1752_);
                v_maxFVar_1779_ = lean_ctor_get(v___x_1778_, 1);
                v_proofInstInfo_1780_ = lean_ctor_get(v___x_1778_, 2);
                v_inferType_1781_ = lean_ctor_get(v___x_1778_, 3);
                v_getLevel_1782_ = lean_ctor_get(v___x_1778_, 4);
                v_congrInfo_1783_ = lean_ctor_get(v___x_1778_, 5);
                v_defEqI_1784_ = lean_ctor_get(v___x_1778_, 6);
                v_extensions_1785_ = lean_ctor_get(v___x_1778_, 7);
                v_issues_1786_ = lean_ctor_get(v___x_1778_, 8);
                v_canon_1787_ = lean_ctor_get(v___x_1778_, 9);
                v_debug_1788_ = lean_ctor_get_uint8(
                    v___x_1778_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1797_ = (!lean_is_exclusive(v___x_1778_)) as u8;
                if v_isSharedCheck_1797_ == 0 {
                    v_unused_1798_ = lean_ctor_get(v___x_1778_, 0);
                    lean_dec(v_unused_1798_);
                    v___x_1790_ = v___x_1778_;
                    v_isShared_1791_ = v_isSharedCheck_1797_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_1787_);
                    lean_inc(v_issues_1786_);
                    lean_inc(v_extensions_1785_);
                    lean_inc(v_defEqI_1784_);
                    lean_inc(v_congrInfo_1783_);
                    lean_inc(v_getLevel_1782_);
                    lean_inc(v_inferType_1781_);
                    lean_inc(v_proofInstInfo_1780_);
                    lean_inc(v_maxFVar_1779_);
                    lean_dec(v___x_1778_);
                    v___x_1790_ = lean_box(0);
                    v_isShared_1791_ = v_isSharedCheck_1797_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1791_ == 0 {
                    lean_ctor_set(v___x_1790_, 0, v_snd_1777_);
                    v___x_1793_ = v___x_1790_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_snd_1777_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_maxFVar_1779_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_proofInstInfo_1780_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_inferType_1781_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_getLevel_1782_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_congrInfo_1783_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 6, v_defEqI_1784_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 7, v_extensions_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 8, v_issues_1786_);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 9, v_canon_1787_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1796_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_1788_,
                    );
                    v___x_1793_ = v_reuseFailAlloc_1796_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1794_ = lean_st_ref_set(v_a_1752_, v___x_1793_);
                v___x_1795_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1795_, 0, v_fst_1776_);
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___boxed(
    mut v_e_1801_: *mut LeanObject,
    mut v_s_1802_: *mut LeanObject,
    mut v_d_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
    mut v_a_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1806_: *mut LeanObject = core::ptr::null_mut();
    v_res_1806_ =
        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_1801_, v_s_1802_, v_d_1803_, v_a_1804_);
    lean_dec(v_a_1804_);
    lean_dec(v_d_1803_);
    lean_dec(v_s_1802_);
    return v_res_1806_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS(
    mut v_e_1807_: *mut LeanObject,
    mut v_s_1808_: *mut LeanObject,
    mut v_d_1809_: *mut LeanObject,
    mut v_a_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1817_ =
        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_1807_, v_s_1808_, v_d_1809_, v_a_1811_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(
    mut v_e_1818_: *mut LeanObject,
    mut v_s_1819_: *mut LeanObject,
    mut v_d_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
    mut v_a_1822_: *mut LeanObject,
    mut v_a_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lean_Meta_Sym_lowerLooseBVarsS(
        v_e_1818_, v_s_1819_, v_d_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_,
        v_a_1826_,
    );
    lean_dec(v_a_1826_);
    lean_dec_ref(v_a_1825_);
    lean_dec(v_a_1824_);
    lean_dec_ref(v_a_1823_);
    lean_dec(v_a_1822_);
    lean_dec_ref(v_a_1821_);
    lean_dec(v_d_1820_);
    lean_dec(v_s_1819_);
    return v_res_1828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(
    mut v_s_1829_: *mut LeanObject,
    mut v_d_1830_: *mut LeanObject,
    mut v_e_1831_: *mut LeanObject,
    mut v_offset_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: u8,
    mut v_a_1835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v_fst_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___y_1855_: u8 = 0;
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_binderName_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1870_: u8 = 0;
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v_fst_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___y_1890_: u8 = 0;
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u8 = 0;
    let mut v___x_1899_: u8 = 0;
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut v_binderName_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1905_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1918_: u8 = 0;
    let mut v_fst_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___y_1925_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1934_: u8 = 0;
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_declName_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1941_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v_fst_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___y_1966_: u8 = 0;
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: u8 = 0;
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_data_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v_fst_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_typeName_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v_fst_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_1831_) {
                5 => {
                    v_fn_1836_ = lean_ctor_get(v_e_1831_, 0);
                    v_arg_1837_ = lean_ctor_get(v_e_1831_, 1);
                    lean_inc(v_offset_1832_);
                    lean_inc_ref(v_fn_1836_);
                    v___x_1838_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_fn_1836_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1839_ = lean_ctor_get(v___x_1838_, 0);
                    lean_inc(v_fst_1839_);
                    v_snd_1840_ = lean_ctor_get(v___x_1838_, 1);
                    lean_inc(v_snd_1840_);
                    lean_dec_ref(v___x_1838_);
                    v_fst_1841_ = lean_ctor_get(v_fst_1839_, 0);
                    lean_inc(v_fst_1841_);
                    v_snd_1842_ = lean_ctor_get(v_fst_1839_, 1);
                    lean_inc(v_snd_1842_);
                    lean_dec(v_fst_1839_);
                    lean_inc_ref(v_arg_1837_);
                    v___x_1843_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_arg_1837_, v_offset_1832_, v_snd_1842_, v_a_1834_, v_snd_1840_);
                    v_fst_1844_ = lean_ctor_get(v___x_1843_, 0);
                    v_snd_1845_ = lean_ctor_get(v___x_1843_, 1);
                    v_isSharedCheck_1866_ = (!lean_is_exclusive(v___x_1843_)) as u8;
                    if v_isSharedCheck_1866_ == 0 {
                        v___x_1847_ = v___x_1843_;
                        v_isShared_1848_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1845_);
                        lean_inc(v_fst_1844_);
                        lean_dec(v___x_1843_);
                        v___x_1847_ = lean_box(0);
                        v_isShared_1848_ = v_isSharedCheck_1866_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_1867_ = lean_ctor_get(v_e_1831_, 0);
                    v_binderType_1868_ = lean_ctor_get(v_e_1831_, 1);
                    v_body_1869_ = lean_ctor_get(v_e_1831_, 2);
                    v_binderInfo_1870_ = lean_ctor_get_uint8(
                        v_e_1831_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_1832_);
                    lean_inc_ref(v_binderType_1868_);
                    v___x_1871_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_binderType_1868_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1872_ = lean_ctor_get(v___x_1871_, 0);
                    lean_inc(v_fst_1872_);
                    v_snd_1873_ = lean_ctor_get(v___x_1871_, 1);
                    lean_inc(v_snd_1873_);
                    lean_dec_ref(v___x_1871_);
                    v_fst_1874_ = lean_ctor_get(v_fst_1872_, 0);
                    lean_inc(v_fst_1874_);
                    v_snd_1875_ = lean_ctor_get(v_fst_1872_, 1);
                    lean_inc(v_snd_1875_);
                    lean_dec(v_fst_1872_);
                    v___x_1876_ = lean_unsigned_to_nat(1);
                    v___x_1877_ = lean_nat_add(v_offset_1832_, v___x_1876_);
                    lean_dec(v_offset_1832_);
                    lean_inc_ref(v_body_1869_);
                    v___x_1878_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_body_1869_, v___x_1877_, v_snd_1875_, v_a_1834_, v_snd_1873_);
                    v_fst_1879_ = lean_ctor_get(v___x_1878_, 0);
                    v_snd_1880_ = lean_ctor_get(v___x_1878_, 1);
                    v_isSharedCheck_1901_ = (!lean_is_exclusive(v___x_1878_)) as u8;
                    if v_isSharedCheck_1901_ == 0 {
                        v___x_1882_ = v___x_1878_;
                        v_isShared_1883_ = v_isSharedCheck_1901_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_1880_);
                        lean_inc(v_fst_1879_);
                        lean_dec(v___x_1878_);
                        v___x_1882_ = lean_box(0);
                        v_isShared_1883_ = v_isSharedCheck_1901_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_1902_ = lean_ctor_get(v_e_1831_, 0);
                    v_binderType_1903_ = lean_ctor_get(v_e_1831_, 1);
                    v_body_1904_ = lean_ctor_get(v_e_1831_, 2);
                    v_binderInfo_1905_ = lean_ctor_get_uint8(
                        v_e_1831_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_1832_);
                    lean_inc_ref(v_binderType_1903_);
                    v___x_1906_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_binderType_1903_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1907_ = lean_ctor_get(v___x_1906_, 0);
                    lean_inc(v_fst_1907_);
                    v_snd_1908_ = lean_ctor_get(v___x_1906_, 1);
                    lean_inc(v_snd_1908_);
                    lean_dec_ref(v___x_1906_);
                    v_fst_1909_ = lean_ctor_get(v_fst_1907_, 0);
                    lean_inc(v_fst_1909_);
                    v_snd_1910_ = lean_ctor_get(v_fst_1907_, 1);
                    lean_inc(v_snd_1910_);
                    lean_dec(v_fst_1907_);
                    v___x_1911_ = lean_unsigned_to_nat(1);
                    v___x_1912_ = lean_nat_add(v_offset_1832_, v___x_1911_);
                    lean_dec(v_offset_1832_);
                    lean_inc_ref(v_body_1904_);
                    v___x_1913_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_body_1904_, v___x_1912_, v_snd_1910_, v_a_1834_, v_snd_1908_);
                    v_fst_1914_ = lean_ctor_get(v___x_1913_, 0);
                    v_snd_1915_ = lean_ctor_get(v___x_1913_, 1);
                    v_isSharedCheck_1936_ = (!lean_is_exclusive(v___x_1913_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v___x_1917_ = v___x_1913_;
                        v_isShared_1918_ = v_isSharedCheck_1936_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_1915_);
                        lean_inc(v_fst_1914_);
                        lean_dec(v___x_1913_);
                        v___x_1917_ = lean_box(0);
                        v_isShared_1918_ = v_isSharedCheck_1936_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_1937_ = lean_ctor_get(v_e_1831_, 0);
                    v_type_1938_ = lean_ctor_get(v_e_1831_, 1);
                    v_value_1939_ = lean_ctor_get(v_e_1831_, 2);
                    v_body_1940_ = lean_ctor_get(v_e_1831_, 3);
                    v_nondep_1941_ = lean_ctor_get_uint8(
                        v_e_1831_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_n(v_offset_1832_, 2);
                    lean_inc_ref(v_type_1938_);
                    v___x_1942_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_type_1938_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1943_ = lean_ctor_get(v___x_1942_, 0);
                    lean_inc(v_fst_1943_);
                    v_snd_1944_ = lean_ctor_get(v___x_1942_, 1);
                    lean_inc(v_snd_1944_);
                    lean_dec_ref(v___x_1942_);
                    v_fst_1945_ = lean_ctor_get(v_fst_1943_, 0);
                    lean_inc(v_fst_1945_);
                    v_snd_1946_ = lean_ctor_get(v_fst_1943_, 1);
                    lean_inc(v_snd_1946_);
                    lean_dec(v_fst_1943_);
                    lean_inc_ref(v_value_1939_);
                    v___x_1947_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_value_1939_, v_offset_1832_, v_snd_1946_, v_a_1834_, v_snd_1944_);
                    v_fst_1948_ = lean_ctor_get(v___x_1947_, 0);
                    lean_inc(v_fst_1948_);
                    v_snd_1949_ = lean_ctor_get(v___x_1947_, 1);
                    lean_inc(v_snd_1949_);
                    lean_dec_ref(v___x_1947_);
                    v_fst_1950_ = lean_ctor_get(v_fst_1948_, 0);
                    lean_inc(v_fst_1950_);
                    v_snd_1951_ = lean_ctor_get(v_fst_1948_, 1);
                    lean_inc(v_snd_1951_);
                    lean_dec(v_fst_1948_);
                    v___x_1952_ = lean_unsigned_to_nat(1);
                    v___x_1953_ = lean_nat_add(v_offset_1832_, v___x_1952_);
                    lean_dec(v_offset_1832_);
                    lean_inc_ref(v_body_1940_);
                    v___x_1954_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_body_1940_, v___x_1953_, v_snd_1951_, v_a_1834_, v_snd_1949_);
                    v_fst_1955_ = lean_ctor_get(v___x_1954_, 0);
                    v_snd_1956_ = lean_ctor_get(v___x_1954_, 1);
                    v_isSharedCheck_1979_ = (!lean_is_exclusive(v___x_1954_)) as u8;
                    if v_isSharedCheck_1979_ == 0 {
                        v___x_1958_ = v___x_1954_;
                        v_isShared_1959_ = v_isSharedCheck_1979_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_snd_1956_);
                        lean_inc(v_fst_1955_);
                        lean_dec(v___x_1954_);
                        v___x_1958_ = lean_box(0);
                        v_isShared_1959_ = v_isSharedCheck_1979_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_1980_ = lean_ctor_get(v_e_1831_, 0);
                    v_expr_1981_ = lean_ctor_get(v_e_1831_, 1);
                    lean_inc_ref(v_expr_1981_);
                    v___x_1982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_expr_1981_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_1983_ = lean_ctor_get(v___x_1982_, 0);
                    v_snd_1984_ = lean_ctor_get(v___x_1982_, 1);
                    v_isSharedCheck_2002_ = (!lean_is_exclusive(v___x_1982_)) as u8;
                    if v_isSharedCheck_2002_ == 0 {
                        v___x_1986_ = v___x_1982_;
                        v_isShared_1987_ = v_isSharedCheck_2002_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_snd_1984_);
                        lean_inc(v_fst_1983_);
                        lean_dec(v___x_1982_);
                        v___x_1986_ = lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_2002_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_2003_ = lean_ctor_get(v_e_1831_, 0);
                    v_idx_2004_ = lean_ctor_get(v_e_1831_, 1);
                    v_struct_2005_ = lean_ctor_get(v_e_1831_, 2);
                    lean_inc_ref(v_struct_2005_);
                    v___x_2006_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_1829_, v_d_1830_, v_struct_2005_, v_offset_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
                    v_fst_2007_ = lean_ctor_get(v___x_2006_, 0);
                    v_snd_2008_ = lean_ctor_get(v___x_2006_, 1);
                    v_isSharedCheck_2026_ = (!lean_is_exclusive(v___x_2006_)) as u8;
                    if v_isSharedCheck_2026_ == 0 {
                        v___x_2010_ = v___x_2006_;
                        v_isShared_2011_ = v_isSharedCheck_2026_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_snd_2008_);
                        lean_inc(v_fst_2007_);
                        lean_dec(v___x_2006_);
                        v___x_2010_ = lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2026_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_offset_1832_);
                    lean_dec_ref(v_e_1831_);
                    v___x_2027_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
                    v___x_2028_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_2027_, v_a_1833_, v_a_1834_, v_a_1835_);
                    return v___x_2028_;
                }
            },
            1 => {
                v_fst_1849_ = lean_ctor_get(v_fst_1844_, 0);
                v_snd_1850_ = lean_ctor_get(v_fst_1844_, 1);
                v_isSharedCheck_1865_ = (!lean_is_exclusive(v_fst_1844_)) as u8;
                if v_isSharedCheck_1865_ == 0 {
                    v___x_1852_ = v_fst_1844_;
                    v_isShared_1853_ = v_isSharedCheck_1865_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1850_);
                    lean_inc(v_fst_1849_);
                    lean_dec(v_fst_1844_);
                    v___x_1852_ = lean_box(0);
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
                    lean_del_object(v___x_1852_);
                    lean_del_object(v___x_1847_);
                    lean_dec_ref_known(v_e_1831_, 2);
                    v___x_1856_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_1841_, v_fst_1849_, v_snd_1850_, v_a_1834_, v_snd_1845_);
                    return v___x_1856_;
                } else {
                    lean_dec(v_fst_1849_);
                    lean_dec(v_fst_1841_);
                    if v_isShared_1853_ == 0 {
                        lean_ctor_set(v___x_1852_, 0, v_e_1831_);
                        v___x_1858_ = v___x_1852_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_e_1831_);
                        lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_snd_1850_);
                        v___x_1858_ = v_reuseFailAlloc_1862_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1848_ == 0 {
                    lean_ctor_set(v___x_1847_, 0, v___x_1858_);
                    v___x_1860_ = v___x_1847_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
                    lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_snd_1845_);
                    v___x_1860_ = v_reuseFailAlloc_1861_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1860_;
            }
            6 => {
                v_fst_1884_ = lean_ctor_get(v_fst_1879_, 0);
                v_snd_1885_ = lean_ctor_get(v_fst_1879_, 1);
                v_isSharedCheck_1900_ = (!lean_is_exclusive(v_fst_1879_)) as u8;
                if v_isSharedCheck_1900_ == 0 {
                    v___x_1887_ = v_fst_1879_;
                    v_isShared_1888_ = v_isSharedCheck_1900_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_1885_);
                    lean_inc(v_fst_1884_);
                    lean_dec(v_fst_1879_);
                    v___x_1887_ = lean_box(0);
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
                    lean_inc(v_binderName_1867_);
                    lean_del_object(v___x_1887_);
                    lean_del_object(v___x_1882_);
                    lean_dec_ref_known(v_e_1831_, 3);
                    v___x_1891_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_1867_, v_binderInfo_1870_, v_fst_1874_, v_fst_1884_, v_snd_1885_, v_a_1834_, v_snd_1880_);
                    return v___x_1891_;
                } else {
                    lean_dec(v_fst_1884_);
                    lean_dec(v_fst_1874_);
                    if v_isShared_1888_ == 0 {
                        lean_ctor_set(v___x_1887_, 0, v_e_1831_);
                        v___x_1893_ = v___x_1887_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_e_1831_);
                        lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_snd_1885_);
                        v___x_1893_ = v_reuseFailAlloc_1897_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1883_ == 0 {
                    lean_ctor_set(v___x_1882_, 0, v___x_1893_);
                    v___x_1895_ = v___x_1882_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_snd_1880_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1895_;
            }
            11 => {
                v_fst_1919_ = lean_ctor_get(v_fst_1914_, 0);
                v_snd_1920_ = lean_ctor_get(v_fst_1914_, 1);
                v_isSharedCheck_1935_ = (!lean_is_exclusive(v_fst_1914_)) as u8;
                if v_isSharedCheck_1935_ == 0 {
                    v___x_1922_ = v_fst_1914_;
                    v_isShared_1923_ = v_isSharedCheck_1935_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_1920_);
                    lean_inc(v_fst_1919_);
                    lean_dec(v_fst_1914_);
                    v___x_1922_ = lean_box(0);
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
                    lean_inc(v_binderName_1902_);
                    lean_del_object(v___x_1922_);
                    lean_del_object(v___x_1917_);
                    lean_dec_ref_known(v_e_1831_, 3);
                    v___x_1926_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_1902_, v_binderInfo_1905_, v_fst_1909_, v_fst_1919_, v_snd_1920_, v_a_1834_, v_snd_1915_);
                    return v___x_1926_;
                } else {
                    lean_dec(v_fst_1919_);
                    lean_dec(v_fst_1909_);
                    if v_isShared_1923_ == 0 {
                        lean_ctor_set(v___x_1922_, 0, v_e_1831_);
                        v___x_1928_ = v___x_1922_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_e_1831_);
                        lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_snd_1920_);
                        v___x_1928_ = v_reuseFailAlloc_1932_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_1918_ == 0 {
                    lean_ctor_set(v___x_1917_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1917_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_snd_1915_);
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1930_;
            }
            16 => {
                v_fst_1960_ = lean_ctor_get(v_fst_1955_, 0);
                v_snd_1961_ = lean_ctor_get(v_fst_1955_, 1);
                v_isSharedCheck_1978_ = (!lean_is_exclusive(v_fst_1955_)) as u8;
                if v_isSharedCheck_1978_ == 0 {
                    v___x_1963_ = v_fst_1955_;
                    v_isShared_1964_ = v_isSharedCheck_1978_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_1961_);
                    lean_inc(v_fst_1960_);
                    lean_dec(v_fst_1955_);
                    v___x_1963_ = lean_box(0);
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
                    lean_inc(v_declName_1937_);
                    lean_del_object(v___x_1963_);
                    lean_del_object(v___x_1958_);
                    lean_dec_ref_known(v_e_1831_, 4);
                    v___x_1967_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1937_, v_fst_1945_, v_fst_1950_, v_fst_1960_, v_nondep_1941_, v_snd_1961_, v_a_1834_, v_snd_1956_);
                    return v___x_1967_;
                } else {
                    v___x_1968_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_1940_,
                            v_fst_1960_,
                        );
                    if v___x_1968_ == 0 {
                        lean_inc(v_declName_1937_);
                        lean_del_object(v___x_1963_);
                        lean_del_object(v___x_1958_);
                        lean_dec_ref_known(v_e_1831_, 4);
                        v___x_1969_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_1937_, v_fst_1945_, v_fst_1950_, v_fst_1960_, v_nondep_1941_, v_snd_1961_, v_a_1834_, v_snd_1956_);
                        return v___x_1969_;
                    } else {
                        lean_dec(v_fst_1960_);
                        lean_dec(v_fst_1950_);
                        lean_dec(v_fst_1945_);
                        if v_isShared_1964_ == 0 {
                            lean_ctor_set(v___x_1963_, 0, v_e_1831_);
                            v___x_1971_ = v___x_1963_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_e_1831_);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_snd_1961_);
                            v___x_1971_ = v_reuseFailAlloc_1975_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1959_ == 0 {
                    lean_ctor_set(v___x_1958_, 0, v___x_1971_);
                    v___x_1973_ = v___x_1958_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_snd_1956_);
                    v___x_1973_ = v_reuseFailAlloc_1974_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1973_;
            }
            21 => {
                v_fst_1988_ = lean_ctor_get(v_fst_1983_, 0);
                v_snd_1989_ = lean_ctor_get(v_fst_1983_, 1);
                v_isSharedCheck_2001_ = (!lean_is_exclusive(v_fst_1983_)) as u8;
                if v_isSharedCheck_2001_ == 0 {
                    v___x_1991_ = v_fst_1983_;
                    v_isShared_1992_ = v_isSharedCheck_2001_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_1989_);
                    lean_inc(v_fst_1988_);
                    lean_dec(v_fst_1983_);
                    v___x_1991_ = lean_box(0);
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
                    lean_inc(v_data_1980_);
                    lean_del_object(v___x_1991_);
                    lean_del_object(v___x_1986_);
                    lean_dec_ref_known(v_e_1831_, 2);
                    v___x_1994_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_1980_, v_fst_1988_, v_snd_1989_, v_a_1834_, v_snd_1984_);
                    return v___x_1994_;
                } else {
                    lean_dec(v_fst_1988_);
                    if v_isShared_1992_ == 0 {
                        lean_ctor_set(v___x_1991_, 0, v_e_1831_);
                        v___x_1996_ = v___x_1991_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_e_1831_);
                        lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_snd_1989_);
                        v___x_1996_ = v_reuseFailAlloc_2000_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1987_ == 0 {
                    lean_ctor_set(v___x_1986_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1986_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
                    lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_snd_1984_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1998_;
            }
            25 => {
                v_fst_2012_ = lean_ctor_get(v_fst_2007_, 0);
                v_snd_2013_ = lean_ctor_get(v_fst_2007_, 1);
                v_isSharedCheck_2025_ = (!lean_is_exclusive(v_fst_2007_)) as u8;
                if v_isSharedCheck_2025_ == 0 {
                    v___x_2015_ = v_fst_2007_;
                    v_isShared_2016_ = v_isSharedCheck_2025_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_2013_);
                    lean_inc(v_fst_2012_);
                    lean_dec(v_fst_2007_);
                    v___x_2015_ = lean_box(0);
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
                    lean_inc(v_idx_2004_);
                    lean_inc(v_typeName_2003_);
                    lean_del_object(v___x_2015_);
                    lean_del_object(v___x_2010_);
                    lean_dec_ref_known(v_e_1831_, 3);
                    v___x_2018_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_2003_, v_idx_2004_, v_fst_2012_, v_snd_2013_, v_a_1834_, v_snd_2008_);
                    return v___x_2018_;
                } else {
                    lean_dec(v_fst_2012_);
                    if v_isShared_2016_ == 0 {
                        lean_ctor_set(v___x_2015_, 0, v_e_1831_);
                        v___x_2020_ = v___x_2015_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_e_1831_);
                        lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_snd_2013_);
                        v___x_2020_ = v_reuseFailAlloc_2024_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2011_ == 0 {
                    lean_ctor_set(v___x_2010_, 0, v___x_2020_);
                    v___x_2022_ = v___x_2010_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
                    lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_snd_2008_);
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
    mut v_s_2029_: *mut LeanObject,
    mut v_d_2030_: *mut LeanObject,
    mut v_e_2031_: *mut LeanObject,
    mut v_offset_2032_: *mut LeanObject,
    mut v_a_2033_: *mut LeanObject,
    mut v_a_2034_: u8,
    mut v_a_2035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_u2081_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v_deBruijnIndex_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_offset_2032_);
                lean_inc_ref(v_e_2031_);
                v_key_2036_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_key_2036_, 0, v_e_2031_);
                lean_ctor_set(v_key_2036_, 1, v_offset_2032_);
                v___x_2051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_2033_, v_key_2036_);
                if lean_obj_tag(v___x_2051_) == 1 {
                    lean_dec_ref_known(v_key_2036_, 2);
                    lean_dec(v_offset_2032_);
                    lean_dec_ref(v_e_2031_);
                    v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
                    lean_inc(v_val_2052_);
                    lean_dec_ref_known(v___x_2051_, 1);
                    v___x_2053_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2053_, 0, v_val_2052_);
                    lean_ctor_set(v___x_2053_, 1, v_a_2033_);
                    v___x_2054_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2054_, 0, v___x_2053_);
                    lean_ctor_set(v___x_2054_, 1, v_a_2035_);
                    return v___x_2054_;
                } else {
                    lean_dec(v___x_2051_);
                    v_s_u2081_2055_ = lean_nat_add(v_s_2029_, v_offset_2032_);
                    v___x_2056_ = l_Lean_Expr_looseBVarRange(v_e_2031_);
                    v___x_2057_ = lean_nat_dec_le(v___x_2056_, v_s_u2081_2055_);
                    lean_dec(v___x_2056_);
                    if v___x_2057_ == 0 {
                        if lean_obj_tag(v_e_2031_) == 0 {
                            v_deBruijnIndex_2058_ = lean_ctor_get(v_e_2031_, 0);
                            v___x_2059_ = lean_nat_dec_le(v_s_u2081_2055_, v_deBruijnIndex_2058_);
                            lean_dec(v_s_u2081_2055_);
                            if v___x_2059_ == 0 {
                                v_snd_2038_ = v_a_2035_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_deBruijnIndex_2058_);
                                lean_dec_ref_known(v_e_2031_, 1);
                                lean_dec(v_offset_2032_);
                                v___x_2060_ = lean_nat_add(v_deBruijnIndex_2058_, v_d_2030_);
                                lean_dec(v_deBruijnIndex_2058_);
                                v___x_2061_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_2060_, v_a_2035_);
                                v_fst_2062_ = lean_ctor_get(v___x_2061_, 0);
                                lean_inc(v_fst_2062_);
                                v_snd_2063_ = lean_ctor_get(v___x_2061_, 1);
                                lean_inc(v_snd_2063_);
                                lean_dec_ref(v___x_2061_);
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
                            lean_dec(v_s_u2081_2055_);
                            v_snd_2038_ = v_a_2035_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_s_u2081_2055_);
                        lean_dec(v_offset_2032_);
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
            1 => match lean_obj_tag(v_e_2031_) {
                9 => {
                    lean_dec(v_offset_2032_);
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
                    lean_dec(v_offset_2032_);
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
                    lean_dec(v_offset_2032_);
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
                    lean_dec(v_offset_2032_);
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
                    lean_dec(v_offset_2032_);
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
                    lean_dec(v_offset_2032_);
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
                    v_fst_2046_ = lean_ctor_get(v___x_2045_, 0);
                    lean_inc(v_fst_2046_);
                    v_snd_2047_ = lean_ctor_get(v___x_2045_, 1);
                    lean_inc(v_snd_2047_);
                    lean_dec_ref(v___x_2045_);
                    v_fst_2048_ = lean_ctor_get(v_fst_2046_, 0);
                    lean_inc(v_fst_2048_);
                    v_snd_2049_ = lean_ctor_get(v_fst_2046_, 1);
                    lean_inc(v_snd_2049_);
                    lean_dec(v_fst_2046_);
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
    mut v_s_2066_: *mut LeanObject,
    mut v_d_2067_: *mut LeanObject,
    mut v_e_2068_: *mut LeanObject,
    mut v_offset_2069_: *mut LeanObject,
    mut v_a_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2073_: u8 = 0;
    let mut v_res_2074_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2073_ = (lean_unbox(v_a_2071_) as u8);
    v_res_2074_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_2066_, v_d_2067_, v_e_2068_, v_offset_2069_, v_a_2070_, v_a_boxed_2073_, v_a_2072_);
    lean_dec(v_d_2067_);
    lean_dec(v_s_2066_);
    return v_res_2074_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(
    mut v_s_2075_: *mut LeanObject,
    mut v_d_2076_: *mut LeanObject,
    mut v_e_2077_: *mut LeanObject,
    mut v_offset_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2082_: u8 = 0;
    let mut v_res_2083_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2082_ = (lean_unbox(v_a_2080_) as u8);
    v_res_2083_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_2075_, v_d_2076_, v_e_2077_, v_offset_2078_, v_a_2079_, v_a_boxed_2082_, v_a_2081_);
    lean_dec(v_d_2076_);
    lean_dec(v_s_2075_);
    return v_res_2083_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS_x27(
    mut v_e_2084_: *mut LeanObject,
    mut v_s_2085_: *mut LeanObject,
    mut v_d_2086_: *mut LeanObject,
    mut v_a_2087_: u8,
    mut v_a_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: u8 = 0;
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_unused_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2089_ = l_Lean_Expr_looseBVarRange(v_e_2084_);
                v___x_2090_ = lean_nat_dec_le(v___x_2089_, v_s_2085_);
                lean_dec(v___x_2089_);
                if v___x_2090_ == 0 {
                    v___x_2091_ = lean_unsigned_to_nat(0);
                    if lean_obj_tag(v_e_2084_) == 0 {
                        v_deBruijnIndex_2113_ = lean_ctor_get(v_e_2084_, 0);
                        v___x_2114_ = lean_nat_dec_le(v_s_2085_, v_deBruijnIndex_2113_);
                        if v___x_2114_ == 0 {
                            v_snd_2093_ = v_a_2088_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_deBruijnIndex_2113_);
                            lean_dec_ref_known(v_e_2084_, 1);
                            v___x_2115_ = lean_nat_add(v_deBruijnIndex_2113_, v_d_2086_);
                            lean_dec(v_deBruijnIndex_2113_);
                            v___x_2116_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_2115_, v_a_2088_);
                            return v___x_2116_;
                        }
                    } else {
                        v_snd_2093_ = v_a_2088_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2117_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2117_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2117_, 1, v_a_2088_);
                    return v___x_2117_;
                }
            }
            1 => match lean_obj_tag(v_e_2084_) {
                9 => {
                    v___x_2094_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2094_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2094_, 1, v_snd_2093_);
                    return v___x_2094_;
                }
                2 => {
                    v___x_2095_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2095_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2095_, 1, v_snd_2093_);
                    return v___x_2095_;
                }
                0 => {
                    v___x_2096_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2096_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2096_, 1, v_snd_2093_);
                    return v___x_2096_;
                }
                1 => {
                    v___x_2097_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2097_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2097_, 1, v_snd_2093_);
                    return v___x_2097_;
                }
                4 => {
                    v___x_2098_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2098_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2098_, 1, v_snd_2093_);
                    return v___x_2098_;
                }
                3 => {
                    v___x_2099_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2099_, 0, v_e_2084_);
                    lean_ctor_set(v___x_2099_, 1, v_snd_2093_);
                    return v___x_2099_;
                }
                _ => {
                    v___x_2100_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1,
                    );
                    v___x_2101_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_2085_, v_d_2086_, v_e_2084_, v___x_2091_, v___x_2100_, v_a_2087_, v_snd_2093_);
                    v_fst_2102_ = lean_ctor_get(v___x_2101_, 0);
                    lean_inc(v_fst_2102_);
                    v_snd_2103_ = lean_ctor_get(v___x_2101_, 1);
                    lean_inc(v_snd_2103_);
                    lean_dec_ref(v___x_2101_);
                    v_fst_2104_ = lean_ctor_get(v_fst_2102_, 0);
                    v_isSharedCheck_2111_ = (!lean_is_exclusive(v_fst_2102_)) as u8;
                    if v_isSharedCheck_2111_ == 0 {
                        v_unused_2112_ = lean_ctor_get(v_fst_2102_, 1);
                        lean_dec(v_unused_2112_);
                        v___x_2106_ = v_fst_2102_;
                        v_isShared_2107_ = v_isSharedCheck_2111_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_2104_);
                        lean_dec(v_fst_2102_);
                        v___x_2106_ = lean_box(0);
                        v_isShared_2107_ = v_isSharedCheck_2111_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => {
                if v_isShared_2107_ == 0 {
                    lean_ctor_set(v___x_2106_, 1, v_snd_2103_);
                    v___x_2109_ = v___x_2106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fst_2104_);
                    lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2103_);
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
    mut v_e_2118_: *mut LeanObject,
    mut v_s_2119_: *mut LeanObject,
    mut v_d_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2123_: u8 = 0;
    let mut v_res_2124_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2123_ = (lean_unbox(v_a_2121_) as u8);
    v_res_2124_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
        v_e_2118_,
        v_s_2119_,
        v_d_2120_,
        v_a_boxed_2123_,
        v_a_2122_,
    );
    lean_dec(v_d_2120_);
    lean_dec(v_s_2119_);
    return v_res_2124_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS___redArg(
    mut v_e_2125_: *mut LeanObject,
    mut v_s_2126_: *mut LeanObject,
    mut v_d_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2141_: u8 = 0;
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2150_: u8 = 0;
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2164_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_unused_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2130_ = lean_st_ref_take(v_a_2128_);
                v_share_2131_ = lean_ctor_get(v___x_2130_, 0);
                v_maxFVar_2132_ = lean_ctor_get(v___x_2130_, 1);
                v_proofInstInfo_2133_ = lean_ctor_get(v___x_2130_, 2);
                v_inferType_2134_ = lean_ctor_get(v___x_2130_, 3);
                v_getLevel_2135_ = lean_ctor_get(v___x_2130_, 4);
                v_congrInfo_2136_ = lean_ctor_get(v___x_2130_, 5);
                v_defEqI_2137_ = lean_ctor_get(v___x_2130_, 6);
                v_extensions_2138_ = lean_ctor_get(v___x_2130_, 7);
                v_issues_2139_ = lean_ctor_get(v___x_2130_, 8);
                v_canon_2140_ = lean_ctor_get(v___x_2130_, 9);
                v_debug_2141_ = lean_ctor_get_uint8(
                    v___x_2130_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2176_ = (!lean_is_exclusive(v___x_2130_)) as u8;
                if v_isSharedCheck_2176_ == 0 {
                    v___x_2143_ = v___x_2130_;
                    v_isShared_2144_ = v_isSharedCheck_2176_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_2140_);
                    lean_inc(v_issues_2139_);
                    lean_inc(v_extensions_2138_);
                    lean_inc(v_defEqI_2137_);
                    lean_inc(v_congrInfo_2136_);
                    lean_inc(v_getLevel_2135_);
                    lean_inc(v_inferType_2134_);
                    lean_inc(v_proofInstInfo_2133_);
                    lean_inc(v_maxFVar_2132_);
                    lean_inc(v_share_2131_);
                    lean_dec(v___x_2130_);
                    v___x_2143_ = lean_box(0);
                    v_isShared_2144_ = v_isSharedCheck_2176_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2145_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0,
                );
                if v_isShared_2144_ == 0 {
                    lean_ctor_set(v___x_2143_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2145_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_maxFVar_2132_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_proofInstInfo_2133_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_inferType_2134_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_getLevel_2135_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_congrInfo_2136_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_defEqI_2137_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_extensions_2138_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_issues_2139_);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 9, v_canon_2140_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2175_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_2150_ = lean_ctor_get_uint8(
                    v___x_2149_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2149_);
                v___x_2151_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                    v_e_2125_,
                    v_s_2126_,
                    v_d_2127_,
                    v_debug_2150_,
                    v_share_2131_,
                );
                v_fst_2152_ = lean_ctor_get(v___x_2151_, 0);
                lean_inc(v_fst_2152_);
                v_snd_2153_ = lean_ctor_get(v___x_2151_, 1);
                lean_inc(v_snd_2153_);
                lean_dec_ref(v___x_2151_);
                v___x_2154_ = lean_st_ref_take(v_a_2128_);
                v_maxFVar_2155_ = lean_ctor_get(v___x_2154_, 1);
                v_proofInstInfo_2156_ = lean_ctor_get(v___x_2154_, 2);
                v_inferType_2157_ = lean_ctor_get(v___x_2154_, 3);
                v_getLevel_2158_ = lean_ctor_get(v___x_2154_, 4);
                v_congrInfo_2159_ = lean_ctor_get(v___x_2154_, 5);
                v_defEqI_2160_ = lean_ctor_get(v___x_2154_, 6);
                v_extensions_2161_ = lean_ctor_get(v___x_2154_, 7);
                v_issues_2162_ = lean_ctor_get(v___x_2154_, 8);
                v_canon_2163_ = lean_ctor_get(v___x_2154_, 9);
                v_debug_2164_ = lean_ctor_get_uint8(
                    v___x_2154_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2173_ = (!lean_is_exclusive(v___x_2154_)) as u8;
                if v_isSharedCheck_2173_ == 0 {
                    v_unused_2174_ = lean_ctor_get(v___x_2154_, 0);
                    lean_dec(v_unused_2174_);
                    v___x_2166_ = v___x_2154_;
                    v_isShared_2167_ = v_isSharedCheck_2173_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_2163_);
                    lean_inc(v_issues_2162_);
                    lean_inc(v_extensions_2161_);
                    lean_inc(v_defEqI_2160_);
                    lean_inc(v_congrInfo_2159_);
                    lean_inc(v_getLevel_2158_);
                    lean_inc(v_inferType_2157_);
                    lean_inc(v_proofInstInfo_2156_);
                    lean_inc(v_maxFVar_2155_);
                    lean_dec(v___x_2154_);
                    v___x_2166_ = lean_box(0);
                    v_isShared_2167_ = v_isSharedCheck_2173_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2167_ == 0 {
                    lean_ctor_set(v___x_2166_, 0, v_snd_2153_);
                    v___x_2169_ = v___x_2166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_snd_2153_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_maxFVar_2155_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_proofInstInfo_2156_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_inferType_2157_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_getLevel_2158_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_congrInfo_2159_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_defEqI_2160_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_extensions_2161_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_issues_2162_);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 9, v_canon_2163_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2172_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2164_,
                    );
                    v___x_2169_ = v_reuseFailAlloc_2172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2170_ = lean_st_ref_set(v_a_2128_, v___x_2169_);
                v___x_2171_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2171_, 0, v_fst_2152_);
                return v___x_2171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS___redArg___boxed(
    mut v_e_2177_: *mut LeanObject,
    mut v_s_2178_: *mut LeanObject,
    mut v_d_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2182_: *mut LeanObject = core::ptr::null_mut();
    v_res_2182_ =
        l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_2177_, v_s_2178_, v_d_2179_, v_a_2180_);
    lean_dec(v_a_2180_);
    lean_dec(v_d_2179_);
    lean_dec(v_s_2178_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS(
    mut v_e_2183_: *mut LeanObject,
    mut v_s_2184_: *mut LeanObject,
    mut v_d_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
    mut v_a_2188_: *mut LeanObject,
    mut v_a_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    v___x_2193_ =
        l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_2183_, v_s_2184_, v_d_2185_, v_a_2187_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Meta_Sym_liftLooseBVarsS___boxed(
    mut v_e_2194_: *mut LeanObject,
    mut v_s_2195_: *mut LeanObject,
    mut v_d_2196_: *mut LeanObject,
    mut v_a_2197_: *mut LeanObject,
    mut v_a_2198_: *mut LeanObject,
    mut v_a_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2204_: *mut LeanObject = core::ptr::null_mut();
    v_res_2204_ = l_Lean_Meta_Sym_liftLooseBVarsS(
        v_e_2194_, v_s_2195_, v_d_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_,
        v_a_2202_,
    );
    lean_dec(v_a_2202_);
    lean_dec_ref(v_a_2201_);
    lean_dec(v_a_2200_);
    lean_dec_ref(v_a_2199_);
    lean_dec(v_a_2198_);
    lean_dec_ref(v_a_2197_);
    lean_dec(v_d_2196_);
    lean_dec(v_s_2195_);
    return v_res_2204_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_LooseBVarsS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_LooseBVarsS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
}
