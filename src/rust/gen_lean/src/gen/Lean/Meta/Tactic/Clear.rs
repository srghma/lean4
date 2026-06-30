// Lean compiler output
// Module: Lean.Meta.Tactic.Clear
// Imports: Lean.Meta.Tactic.Util Init.Data.Nat.Order Init.Data.Order.Lemmas
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_uget, lean_array_uget_borrowed, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop, l_Array_eraseIdx___redArg,
};
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_contains, l_Lean_LocalContext_sortFVarsByContextOrder,
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_toExpr, lean_local_ctx_erase,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getDecl,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_mkFreshExprMVarAt,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_Meta_throwTacticEx___redArg, runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit;
pub static l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 108, 101, 97, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0_value) as *mut leanh::LeanObject,1016054550297021175 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [118, 97, 114, 105, 97, 98, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [39, 32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_clear___lam__1___closed__0_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            116, 97, 114, 103, 101, 116, 32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32,
            39, 0,
        ],
    };
static mut l_Lean_MVarId_clear___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clear___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_clear___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_clear___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_clear___lam__1___closed__2_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_MVarId_clear___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clear___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_clear___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_clear___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(
    mut v_fvarId_1378_: *mut leanh::LeanObject,
    mut v_x_1379_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1380_: u8 = 0;
    v___x_1380_ = l_Lean_instBEqFVarId_beq(v_fvarId_1378_, v_x_1379_);
    return v___x_1380_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed(
    mut v_fvarId_1381_: *mut leanh::LeanObject,
    mut v_x_1382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1383_: u8 = 0;
    let mut v_r_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(
        v_fvarId_1381_,
        v_x_1382_,
    );
    leanh::lean_dec(v_x_1382_);
    leanh::lean_dec(v_fvarId_1381_);
    v_r_1384_ = leanh::lean_box((v_res_1383_) as usize);
    return v_r_1384_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(
    mut v_x_1385_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1386_: u8 = 0;
    v___x_1386_ = 0;
    return v___x_1386_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed(
    mut v_x_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1388_: u8 = 0;
    let mut v_r_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ =
        l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(v_x_1387_);
    leanh::lean_dec(v_x_1387_);
    v_r_1389_ = leanh::lean_box((v_res_1388_) as usize);
    return v_r_1389_;
}
pub unsafe fn _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = leanh::lean_box(0);
    v___x_1392_ = leanh::lean_unsigned_to_nat(16);
    v___x_1393_ = lean_mk_array(v___x_1392_, v___x_1391_);
    return v___x_1393_;
}
pub unsafe fn _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once
        ),
        _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1,
    );
    v___x_1395_ = leanh::lean_unsigned_to_nat(0);
    v___x_1396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1396_, 0, v___x_1395_);
    leanh::lean_ctor_set(v___x_1396_, 1, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(
    mut v_localDecl_1397_: *mut leanh::LeanObject,
    mut v_fvarId_1398_: *mut leanh::LeanObject,
    mut v_generalizeNondepLet_1399_: u8,
    mut v___y_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1403_: u8 = 0;
    let mut v_snd_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_unused_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v___f_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1432_: u8 = 0;
    let mut v_mctx_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_unused_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v_mctx_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1465_: u8 = 0;
    let mut v_fst_1467_: u8 = 0;
    let mut v_snd_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1489_: u8 = 0;
    let mut v_mctx_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut v_unused_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v_mctx_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1427_ = leanh::lean_alloc_closure(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1427_, 0, v_fvarId_1398_);
                v___f_1428_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0;
                if leanh::lean_obj_tag(v_localDecl_1397_) == 0 {
                    v_type_1429_ = leanh::lean_ctor_get(v_localDecl_1397_, 3);
                    leanh::lean_inc_ref(v_type_1429_);
                    leanh::lean_dec_ref_known(v_localDecl_1397_, 4);
                    v___x_1430_ = lean_st_ref_get(v___y_1400_);
                    v_mctx_1456_ = leanh::lean_ctor_get(v___x_1430_, 0);
                    leanh::lean_inc_ref_n(v_mctx_1456_, 2);
                    leanh::lean_dec(v___x_1430_);
                    v___x_1457_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
                    v___x_1458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
                    leanh::lean_ctor_set(v___x_1458_, 1, v_mctx_1456_);
                    v___x_1459_ = l_Lean_Expr_hasFVar(v_type_1429_);
                    if v___x_1459_ == 0 {
                        v___x_1460_ = l_Lean_Expr_hasMVar(v_type_1429_);
                        if v___x_1460_ == 0 {
                            leanh::lean_dec_ref_known(v___x_1458_, 2);
                            leanh::lean_dec_ref(v_type_1429_);
                            leanh::lean_dec_ref(v___f_1427_);
                            v_fst_1432_ = v___x_1460_;
                            v_mctx_1433_ = v_mctx_1456_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_mctx_1456_);
                            v___x_1461_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_1427_,
                                    v___f_1428_,
                                    v_type_1429_,
                                    v___x_1458_,
                                );
                            v___y_1451_ = v___x_1461_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_mctx_1456_);
                        v___x_1462_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_1427_,
                            v___f_1428_,
                            v_type_1429_,
                            v___x_1458_,
                        );
                        v___y_1451_ = v___x_1462_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_type_1463_ = leanh::lean_ctor_get(v_localDecl_1397_, 3);
                    leanh::lean_inc_ref(v_type_1463_);
                    v_value_1464_ = leanh::lean_ctor_get(v_localDecl_1397_, 4);
                    leanh::lean_inc_ref(v_value_1464_);
                    v_nondep_1465_ = leanh::lean_ctor_get_uint8(
                        v_localDecl_1397_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    leanh::lean_dec_ref_known(v_localDecl_1397_, 5);
                    if v_generalizeNondepLet_1399_ == 0 {
                        state = 11;
                        continue;
                    } else {
                        if v_nondep_1465_ == 0 {
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_value_1464_);
                            v___x_1487_ = lean_st_ref_get(v___y_1400_);
                            v_mctx_1513_ = leanh::lean_ctor_get(v___x_1487_, 0);
                            leanh::lean_inc_ref_n(v_mctx_1513_, 2);
                            leanh::lean_dec(v___x_1487_);
                            v___x_1514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
                            v___x_1515_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1515_, 0, v___x_1514_);
                            leanh::lean_ctor_set(v___x_1515_, 1, v_mctx_1513_);
                            v___x_1516_ = l_Lean_Expr_hasFVar(v_type_1463_);
                            if v___x_1516_ == 0 {
                                v___x_1517_ = l_Lean_Expr_hasMVar(v_type_1463_);
                                if v___x_1517_ == 0 {
                                    leanh::lean_dec_ref_known(v___x_1515_, 2);
                                    leanh::lean_dec_ref(v_type_1463_);
                                    leanh::lean_dec_ref(v___f_1427_);
                                    v_fst_1489_ = v___x_1517_;
                                    v_mctx_1490_ = v_mctx_1513_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_mctx_1513_);
                                    v___x_1518_ =
                                        l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                            v___f_1427_,
                                            v___f_1428_,
                                            v_type_1463_,
                                            v___x_1515_,
                                        );
                                    v___y_1508_ = v___x_1518_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_mctx_1513_);
                                v___x_1519_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_1427_,
                                        v___f_1428_,
                                        v_type_1463_,
                                        v___x_1515_,
                                    );
                                v___y_1508_ = v___x_1519_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_mctx_1405_ = leanh::lean_ctor_get(v_snd_1404_, 1);
                leanh::lean_inc_ref(v_mctx_1405_);
                leanh::lean_dec_ref(v_snd_1404_);
                v___x_1406_ = lean_st_ref_take(v___y_1400_);
                v_cache_1407_ = leanh::lean_ctor_get(v___x_1406_, 1);
                v_zetaDeltaFVarIds_1408_ = leanh::lean_ctor_get(v___x_1406_, 2);
                v_postponed_1409_ = leanh::lean_ctor_get(v___x_1406_, 3);
                v_diag_1410_ = leanh::lean_ctor_get(v___x_1406_, 4);
                v_isSharedCheck_1420_ = (!leanh::lean_is_exclusive(v___x_1406_)) as u8;
                if v_isSharedCheck_1420_ == 0 {
                    v_unused_1421_ = leanh::lean_ctor_get(v___x_1406_, 0);
                    leanh::lean_dec(v_unused_1421_);
                    v___x_1412_ = v___x_1406_;
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1410_);
                    leanh::lean_inc(v_postponed_1409_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1408_);
                    leanh::lean_inc(v_cache_1407_);
                    leanh::lean_dec(v___x_1406_);
                    v___x_1412_ = leanh::lean_box(0);
                    v_isShared_1413_ = v_isSharedCheck_1420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1413_ == 0 {
                    leanh::lean_ctor_set(v___x_1412_, 0, v_mctx_1405_);
                    v___x_1415_ = v___x_1412_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_mctx_1405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_cache_1407_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1419_,
                        2,
                        v_zetaDeltaFVarIds_1408_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_postponed_1409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_diag_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1419_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1416_ = lean_st_ref_set(v___y_1400_, v___x_1415_);
                v___x_1417_ = leanh::lean_box((v_fst_1403_) as usize);
                v___x_1418_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
                return v___x_1418_;
            }
            4 => {
                v_fst_1424_ = leanh::lean_ctor_get(v___y_1423_, 0);
                leanh::lean_inc(v_fst_1424_);
                v_snd_1425_ = leanh::lean_ctor_get(v___y_1423_, 1);
                leanh::lean_inc(v_snd_1425_);
                leanh::lean_dec_ref(v___y_1423_);
                v___x_1426_ = (leanh::lean_unbox(v_fst_1424_) as u8);
                leanh::lean_dec(v_fst_1424_);
                v_fst_1403_ = v___x_1426_;
                v_snd_1404_ = v_snd_1425_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1434_ = lean_st_ref_take(v___y_1400_);
                v_cache_1435_ = leanh::lean_ctor_get(v___x_1434_, 1);
                v_zetaDeltaFVarIds_1436_ = leanh::lean_ctor_get(v___x_1434_, 2);
                v_postponed_1437_ = leanh::lean_ctor_get(v___x_1434_, 3);
                v_diag_1438_ = leanh::lean_ctor_get(v___x_1434_, 4);
                v_isSharedCheck_1448_ = (!leanh::lean_is_exclusive(v___x_1434_)) as u8;
                if v_isSharedCheck_1448_ == 0 {
                    v_unused_1449_ = leanh::lean_ctor_get(v___x_1434_, 0);
                    leanh::lean_dec(v_unused_1449_);
                    v___x_1440_ = v___x_1434_;
                    v_isShared_1441_ = v_isSharedCheck_1448_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1438_);
                    leanh::lean_inc(v_postponed_1437_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1436_);
                    leanh::lean_inc(v_cache_1435_);
                    leanh::lean_dec(v___x_1434_);
                    v___x_1440_ = leanh::lean_box(0);
                    v_isShared_1441_ = v_isSharedCheck_1448_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1441_ == 0 {
                    leanh::lean_ctor_set(v___x_1440_, 0, v_mctx_1433_);
                    v___x_1443_ = v___x_1440_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_mctx_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_cache_1435_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1447_,
                        2,
                        v_zetaDeltaFVarIds_1436_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_postponed_1437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_diag_1438_);
                    v___x_1443_ = v_reuseFailAlloc_1447_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1444_ = lean_st_ref_set(v___y_1400_, v___x_1443_);
                v___x_1445_ = leanh::lean_box((v_fst_1432_) as usize);
                v___x_1446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
                return v___x_1446_;
            }
            8 => {
                v_snd_1452_ = leanh::lean_ctor_get(v___y_1451_, 1);
                leanh::lean_inc(v_snd_1452_);
                v_fst_1453_ = leanh::lean_ctor_get(v___y_1451_, 0);
                leanh::lean_inc(v_fst_1453_);
                leanh::lean_dec_ref(v___y_1451_);
                v_mctx_1454_ = leanh::lean_ctor_get(v_snd_1452_, 1);
                leanh::lean_inc_ref(v_mctx_1454_);
                leanh::lean_dec(v_snd_1452_);
                v___x_1455_ = (leanh::lean_unbox(v_fst_1453_) as u8);
                leanh::lean_dec(v_fst_1453_);
                v_fst_1432_ = v___x_1455_;
                v_mctx_1433_ = v_mctx_1454_;
                state = 5;
                continue;
            }
            9 => {
                if v_fst_1467_ == 0 {
                    v___x_1469_ = l_Lean_Expr_hasFVar(v_value_1464_);
                    if v___x_1469_ == 0 {
                        v___x_1470_ = l_Lean_Expr_hasMVar(v_value_1464_);
                        if v___x_1470_ == 0 {
                            leanh::lean_dec_ref(v_value_1464_);
                            leanh::lean_dec_ref(v___f_1427_);
                            v_fst_1403_ = v___x_1470_;
                            v_snd_1404_ = v_snd_1468_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1471_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_1427_,
                                    v___f_1428_,
                                    v_value_1464_,
                                    v_snd_1468_,
                                );
                            v___y_1423_ = v___x_1471_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1472_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_1427_,
                            v___f_1428_,
                            v_value_1464_,
                            v_snd_1468_,
                        );
                        v___y_1423_ = v___x_1472_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_value_1464_);
                    leanh::lean_dec_ref(v___f_1427_);
                    v_fst_1403_ = v_fst_1467_;
                    v_snd_1404_ = v_snd_1468_;
                    state = 1;
                    continue;
                }
            }
            10 => {
                v_fst_1475_ = leanh::lean_ctor_get(v___y_1474_, 0);
                leanh::lean_inc(v_fst_1475_);
                v_snd_1476_ = leanh::lean_ctor_get(v___y_1474_, 1);
                leanh::lean_inc(v_snd_1476_);
                leanh::lean_dec_ref(v___y_1474_);
                v___x_1477_ = (leanh::lean_unbox(v_fst_1475_) as u8);
                leanh::lean_dec(v_fst_1475_);
                v_fst_1467_ = v___x_1477_;
                v_snd_1468_ = v_snd_1476_;
                state = 9;
                continue;
            }
            11 => {
                v___x_1479_ = lean_st_ref_get(v___y_1400_);
                v_mctx_1480_ = leanh::lean_ctor_get(v___x_1479_, 0);
                leanh::lean_inc_ref(v_mctx_1480_);
                leanh::lean_dec(v___x_1479_);
                v___x_1481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
                v___x_1482_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1482_, 0, v___x_1481_);
                leanh::lean_ctor_set(v___x_1482_, 1, v_mctx_1480_);
                v___x_1483_ = l_Lean_Expr_hasFVar(v_type_1463_);
                if v___x_1483_ == 0 {
                    v___x_1484_ = l_Lean_Expr_hasMVar(v_type_1463_);
                    if v___x_1484_ == 0 {
                        leanh::lean_dec_ref(v_type_1463_);
                        v_fst_1467_ = v___x_1484_;
                        v_snd_1468_ = v___x_1482_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v___f_1427_);
                        v___x_1485_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_1427_,
                            v___f_1428_,
                            v_type_1463_,
                            v___x_1482_,
                        );
                        v___y_1474_ = v___x_1485_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v___f_1427_);
                    v___x_1486_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_1427_,
                        v___f_1428_,
                        v_type_1463_,
                        v___x_1482_,
                    );
                    v___y_1474_ = v___x_1486_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_1491_ = lean_st_ref_take(v___y_1400_);
                v_cache_1492_ = leanh::lean_ctor_get(v___x_1491_, 1);
                v_zetaDeltaFVarIds_1493_ = leanh::lean_ctor_get(v___x_1491_, 2);
                v_postponed_1494_ = leanh::lean_ctor_get(v___x_1491_, 3);
                v_diag_1495_ = leanh::lean_ctor_get(v___x_1491_, 4);
                v_isSharedCheck_1505_ = (!leanh::lean_is_exclusive(v___x_1491_)) as u8;
                if v_isSharedCheck_1505_ == 0 {
                    v_unused_1506_ = leanh::lean_ctor_get(v___x_1491_, 0);
                    leanh::lean_dec(v_unused_1506_);
                    v___x_1497_ = v___x_1491_;
                    v_isShared_1498_ = v_isSharedCheck_1505_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1495_);
                    leanh::lean_inc(v_postponed_1494_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1493_);
                    leanh::lean_inc(v_cache_1492_);
                    leanh::lean_dec(v___x_1491_);
                    v___x_1497_ = leanh::lean_box(0);
                    v_isShared_1498_ = v_isSharedCheck_1505_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1498_ == 0 {
                    leanh::lean_ctor_set(v___x_1497_, 0, v_mctx_1490_);
                    v___x_1500_ = v___x_1497_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_mctx_1490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_cache_1492_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1504_,
                        2,
                        v_zetaDeltaFVarIds_1493_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_postponed_1494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_diag_1495_);
                    v___x_1500_ = v_reuseFailAlloc_1504_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1501_ = lean_st_ref_set(v___y_1400_, v___x_1500_);
                v___x_1502_ = leanh::lean_box((v_fst_1489_) as usize);
                v___x_1503_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1503_, 0, v___x_1502_);
                return v___x_1503_;
            }
            15 => {
                v_snd_1509_ = leanh::lean_ctor_get(v___y_1508_, 1);
                leanh::lean_inc(v_snd_1509_);
                v_fst_1510_ = leanh::lean_ctor_get(v___y_1508_, 0);
                leanh::lean_inc(v_fst_1510_);
                leanh::lean_dec_ref(v___y_1508_);
                v_mctx_1511_ = leanh::lean_ctor_get(v_snd_1509_, 1);
                leanh::lean_inc_ref(v_mctx_1511_);
                leanh::lean_dec(v_snd_1509_);
                v___x_1512_ = (leanh::lean_unbox(v_fst_1510_) as u8);
                leanh::lean_dec(v_fst_1510_);
                v_fst_1489_ = v___x_1512_;
                v_mctx_1490_ = v_mctx_1511_;
                state = 12;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(
    mut v_localDecl_1520_: *mut leanh::LeanObject,
    mut v_fvarId_1521_: *mut leanh::LeanObject,
    mut v_generalizeNondepLet_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_generalizeNondepLet_boxed_1525_: u8 = 0;
    let mut v_res_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_generalizeNondepLet_boxed_1525_ =
        (leanh::lean_unbox(v_generalizeNondepLet_1522_) as u8);
    v_res_1526_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(
        v_localDecl_1520_,
        v_fvarId_1521_,
        v_generalizeNondepLet_boxed_1525_,
        v___y_1523_,
    );
    leanh::lean_dec(v___y_1523_);
    return v_res_1526_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(
    mut v_localDecl_1527_: *mut leanh::LeanObject,
    mut v_fvarId_1528_: *mut leanh::LeanObject,
    mut v_generalizeNondepLet_1529_: u8,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(
        v_localDecl_1527_,
        v_fvarId_1528_,
        v_generalizeNondepLet_1529_,
        v___y_1531_,
    );
    return v___x_1535_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(
    mut v_localDecl_1536_: *mut leanh::LeanObject,
    mut v_fvarId_1537_: *mut leanh::LeanObject,
    mut v_generalizeNondepLet_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
    mut v___y_1543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_generalizeNondepLet_boxed_1544_: u8 = 0;
    let mut v_res_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_generalizeNondepLet_boxed_1544_ =
        (leanh::lean_unbox(v_generalizeNondepLet_1538_) as u8);
    v_res_1545_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(
        v_localDecl_1536_,
        v_fvarId_1537_,
        v_generalizeNondepLet_boxed_1544_,
        v___y_1539_,
        v___y_1540_,
        v___y_1541_,
        v___y_1542_,
    );
    leanh::lean_dec(v___y_1542_);
    leanh::lean_dec_ref(v___y_1541_);
    leanh::lean_dec(v___y_1540_);
    leanh::lean_dec_ref(v___y_1539_);
    return v_res_1545_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(
    mut v_e_1546_: *mut leanh::LeanObject,
    mut v_fvarId_1547_: *mut leanh::LeanObject,
    mut v___y_1548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1552_: u8 = 0;
    let mut v_mctx_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_unused_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v_mctx_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1550_ = lean_st_ref_get(v___y_1548_);
                v_mctx_1576_ = leanh::lean_ctor_get(v___x_1550_, 0);
                leanh::lean_inc_ref_n(v_mctx_1576_, 2);
                leanh::lean_dec(v___x_1550_);
                v___f_1577_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0;
                v___f_1578_ = leanh::lean_alloc_closure(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1578_, 0, v_fvarId_1547_);
                v___x_1579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
                v___x_1580_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1580_, 0, v___x_1579_);
                leanh::lean_ctor_set(v___x_1580_, 1, v_mctx_1576_);
                v___x_1581_ = l_Lean_Expr_hasFVar(v_e_1546_);
                if v___x_1581_ == 0 {
                    v___x_1582_ = l_Lean_Expr_hasMVar(v_e_1546_);
                    if v___x_1582_ == 0 {
                        leanh::lean_dec_ref_known(v___x_1580_, 2);
                        leanh::lean_dec_ref(v___f_1578_);
                        leanh::lean_dec_ref(v_e_1546_);
                        v_fst_1552_ = v___x_1582_;
                        v_mctx_1553_ = v_mctx_1576_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_mctx_1576_);
                        v___x_1583_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_1578_,
                            v___f_1577_,
                            v_e_1546_,
                            v___x_1580_,
                        );
                        v___y_1571_ = v___x_1583_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mctx_1576_);
                    v___x_1584_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_1578_,
                        v___f_1577_,
                        v_e_1546_,
                        v___x_1580_,
                    );
                    v___y_1571_ = v___x_1584_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_1554_ = lean_st_ref_take(v___y_1548_);
                v_cache_1555_ = leanh::lean_ctor_get(v___x_1554_, 1);
                v_zetaDeltaFVarIds_1556_ = leanh::lean_ctor_get(v___x_1554_, 2);
                v_postponed_1557_ = leanh::lean_ctor_get(v___x_1554_, 3);
                v_diag_1558_ = leanh::lean_ctor_get(v___x_1554_, 4);
                v_isSharedCheck_1568_ = (!leanh::lean_is_exclusive(v___x_1554_)) as u8;
                if v_isSharedCheck_1568_ == 0 {
                    v_unused_1569_ = leanh::lean_ctor_get(v___x_1554_, 0);
                    leanh::lean_dec(v_unused_1569_);
                    v___x_1560_ = v___x_1554_;
                    v_isShared_1561_ = v_isSharedCheck_1568_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1558_);
                    leanh::lean_inc(v_postponed_1557_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1556_);
                    leanh::lean_inc(v_cache_1555_);
                    leanh::lean_dec(v___x_1554_);
                    v___x_1560_ = leanh::lean_box(0);
                    v_isShared_1561_ = v_isSharedCheck_1568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1561_ == 0 {
                    leanh::lean_ctor_set(v___x_1560_, 0, v_mctx_1553_);
                    v___x_1563_ = v___x_1560_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1567_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_mctx_1553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_cache_1555_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1567_,
                        2,
                        v_zetaDeltaFVarIds_1556_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_postponed_1557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_diag_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1567_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1564_ = lean_st_ref_set(v___y_1548_, v___x_1563_);
                v___x_1565_ = leanh::lean_box((v_fst_1552_) as usize);
                v___x_1566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1566_, 0, v___x_1565_);
                return v___x_1566_;
            }
            4 => {
                v_snd_1572_ = leanh::lean_ctor_get(v___y_1571_, 1);
                leanh::lean_inc(v_snd_1572_);
                v_fst_1573_ = leanh::lean_ctor_get(v___y_1571_, 0);
                leanh::lean_inc(v_fst_1573_);
                leanh::lean_dec_ref(v___y_1571_);
                v_mctx_1574_ = leanh::lean_ctor_get(v_snd_1572_, 1);
                leanh::lean_inc_ref(v_mctx_1574_);
                leanh::lean_dec(v_snd_1572_);
                v___x_1575_ = (leanh::lean_unbox(v_fst_1573_) as u8);
                leanh::lean_dec(v_fst_1573_);
                v_fst_1552_ = v___x_1575_;
                v_mctx_1553_ = v_mctx_1574_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(
    mut v_e_1585_: *mut leanh::LeanObject,
    mut v_fvarId_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(
        v_e_1585_,
        v_fvarId_1586_,
        v___y_1587_,
    );
    leanh::lean_dec(v___y_1587_);
    return v_res_1589_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(
    mut v_e_1590_: *mut leanh::LeanObject,
    mut v_fvarId_1591_: *mut leanh::LeanObject,
    mut v___y_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(
        v_e_1590_,
        v_fvarId_1591_,
        v___y_1593_,
    );
    return v___x_1597_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(
    mut v_e_1598_: *mut leanh::LeanObject,
    mut v_fvarId_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1605_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(
        v_e_1598_,
        v_fvarId_1599_,
        v___y_1600_,
        v___y_1601_,
        v___y_1602_,
        v___y_1603_,
    );
    leanh::lean_dec(v___y_1603_);
    leanh::lean_dec_ref(v___y_1602_);
    leanh::lean_dec(v___y_1601_);
    leanh::lean_dec_ref(v___y_1600_);
    return v_res_1605_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(
    mut v_mvarId_1606_: *mut leanh::LeanObject,
    mut v_x_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
    mut v___y_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_a_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1606_,
                    v_x_1607_,
                    v___y_1608_,
                    v___y_1609_,
                    v___y_1610_,
                    v___y_1611_,
                );
                if leanh::lean_obj_tag(v___x_1613_) == 0 {
                    v_a_1614_ = leanh::lean_ctor_get(v___x_1613_, 0);
                    v_isSharedCheck_1621_ = (!leanh::lean_is_exclusive(v___x_1613_)) as u8;
                    if v_isSharedCheck_1621_ == 0 {
                        v___x_1616_ = v___x_1613_;
                        v_isShared_1617_ = v_isSharedCheck_1621_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1614_);
                        leanh::lean_dec(v___x_1613_);
                        v___x_1616_ = leanh::lean_box(0);
                        v_isShared_1617_ = v_isSharedCheck_1621_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1622_ = leanh::lean_ctor_get(v___x_1613_, 0);
                    v_isSharedCheck_1629_ = (!leanh::lean_is_exclusive(v___x_1613_)) as u8;
                    if v_isSharedCheck_1629_ == 0 {
                        v___x_1624_ = v___x_1613_;
                        v_isShared_1625_ = v_isSharedCheck_1629_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1622_);
                        leanh::lean_dec(v___x_1613_);
                        v___x_1624_ = leanh::lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1629_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1617_ == 0 {
                    v___x_1619_ = v___x_1616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
                    v___x_1619_ = v_reuseFailAlloc_1620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1619_;
            }
            3 => {
                if v_isShared_1625_ == 0 {
                    v___x_1627_ = v___x_1624_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
                    v___x_1627_ = v_reuseFailAlloc_1628_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(
    mut v_mvarId_1630_: *mut leanh::LeanObject,
    mut v_x_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
    mut v___y_1633_: *mut leanh::LeanObject,
    mut v___y_1634_: *mut leanh::LeanObject,
    mut v___y_1635_: *mut leanh::LeanObject,
    mut v___y_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(
        v_mvarId_1630_,
        v_x_1631_,
        v___y_1632_,
        v___y_1633_,
        v___y_1634_,
        v___y_1635_,
    );
    leanh::lean_dec(v___y_1635_);
    leanh::lean_dec_ref(v___y_1634_);
    leanh::lean_dec(v___y_1633_);
    leanh::lean_dec_ref(v___y_1632_);
    return v_res_1637_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(
    mut v_00_u03b1_1638_: *mut leanh::LeanObject,
    mut v_mvarId_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
    mut v___y_1642_: *mut leanh::LeanObject,
    mut v___y_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(
        v_mvarId_1639_,
        v_x_1640_,
        v___y_1641_,
        v___y_1642_,
        v___y_1643_,
        v___y_1644_,
    );
    return v___x_1646_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(
    mut v_00_u03b1_1647_: *mut leanh::LeanObject,
    mut v_mvarId_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(
        v_00_u03b1_1647_,
        v_mvarId_1648_,
        v_x_1649_,
        v___y_1650_,
        v___y_1651_,
        v___y_1652_,
        v___y_1653_,
    );
    leanh::lean_dec(v___y_1653_);
    leanh::lean_dec_ref(v___y_1652_);
    leanh::lean_dec(v___y_1651_);
    leanh::lean_dec_ref(v___y_1650_);
    return v_res_1655_;
}
pub unsafe fn l_Lean_MVarId_clear___lam__0(
    mut v_fvarId_1656_: *mut leanh::LeanObject,
    mut v_localInst_1657_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fvar_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    v_fvar_1658_ = leanh::lean_ctor_get(v_localInst_1657_, 1);
    v___x_1659_ = l_Lean_Expr_fvarId_x21(v_fvar_1658_);
    v___x_1660_ = l_Lean_instBEqFVarId_beq(v___x_1659_, v_fvarId_1656_);
    leanh::lean_dec(v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Lean_MVarId_clear___lam__0___boxed(
    mut v_fvarId_1661_: *mut leanh::LeanObject,
    mut v_localInst_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1663_: u8 = 0;
    let mut v_r_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_MVarId_clear___lam__0(v_fvarId_1661_, v_localInst_1662_);
    leanh::lean_dec_ref(v_localInst_1662_);
    leanh::lean_dec(v_fvarId_1661_);
    v_r_1664_ = leanh::lean_box((v_res_1663_) as usize);
    return v_r_1664_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(
    mut v_x_1665_: *mut leanh::LeanObject,
    mut v_x_1666_: *mut leanh::LeanObject,
    mut v_x_1667_: *mut leanh::LeanObject,
    mut v_x_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1669_ = leanh::lean_ctor_get(v_x_1665_, 0);
                v_vs_1670_ = leanh::lean_ctor_get(v_x_1665_, 1);
                v_isSharedCheck_1694_ = (!leanh::lean_is_exclusive(v_x_1665_)) as u8;
                if v_isSharedCheck_1694_ == 0 {
                    v___x_1672_ = v_x_1665_;
                    v_isShared_1673_ = v_isSharedCheck_1694_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1670_);
                    leanh::lean_inc(v_ks_1669_);
                    leanh::lean_dec(v_x_1665_);
                    v___x_1672_ = leanh::lean_box(0);
                    v_isShared_1673_ = v_isSharedCheck_1694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1674_ = lean_array_get_size(v_ks_1669_);
                v___x_1675_ = lean_nat_dec_lt(v_x_1666_, v___x_1674_);
                if v___x_1675_ == 0 {
                    leanh::lean_dec(v_x_1666_);
                    v___x_1676_ = lean_array_push(v_ks_1669_, v_x_1667_);
                    v___x_1677_ = lean_array_push(v_vs_1670_, v_x_1668_);
                    if v_isShared_1673_ == 0 {
                        leanh::lean_ctor_set(v___x_1672_, 1, v___x_1677_);
                        leanh::lean_ctor_set(v___x_1672_, 0, v___x_1676_);
                        v___x_1679_ = v___x_1672_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1680_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1676_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1677_);
                        v___x_1679_ = v_reuseFailAlloc_1680_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1681_ = lean_array_fget_borrowed(v_ks_1669_, v_x_1666_);
                    v___x_1682_ = l_Lean_instBEqMVarId_beq(v_x_1667_, v_k_x27_1681_);
                    if v___x_1682_ == 0 {
                        if v_isShared_1673_ == 0 {
                            v___x_1684_ = v___x_1672_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1688_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_ks_1669_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_vs_1670_);
                            v___x_1684_ = v_reuseFailAlloc_1688_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1689_ = lean_array_fset(v_ks_1669_, v_x_1666_, v_x_1667_);
                        v___x_1690_ = lean_array_fset(v_vs_1670_, v_x_1666_, v_x_1668_);
                        leanh::lean_dec(v_x_1666_);
                        if v_isShared_1673_ == 0 {
                            leanh::lean_ctor_set(v___x_1672_, 1, v___x_1690_);
                            leanh::lean_ctor_set(v___x_1672_, 0, v___x_1689_);
                            v___x_1692_ = v___x_1672_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1693_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
                            v___x_1692_ = v_reuseFailAlloc_1693_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1679_;
            }
            3 => {
                v___x_1685_ = leanh::lean_unsigned_to_nat(1);
                v___x_1686_ = lean_nat_add(v_x_1666_, v___x_1685_);
                leanh::lean_dec(v_x_1666_);
                v_x_1665_ = v___x_1684_;
                v_x_1666_ = v___x_1686_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(
    mut v_n_1695_: *mut leanh::LeanObject,
    mut v_k_1696_: *mut leanh::LeanObject,
    mut v_v_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = leanh::lean_unsigned_to_nat(0);
    v___x_1699_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_1695_, v___x_1698_, v_k_1696_, v_v_1697_);
    return v___x_1699_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0()
-> usize {
    let mut v___x_1700_: usize = 0;
    let mut v___x_1701_: usize = 0;
    let mut v___x_1702_: usize = 0;
    v___x_1700_ = 5usize;
    v___x_1701_ = 1usize;
    v___x_1702_ = lean_usize_shift_left(v___x_1701_, v___x_1700_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1()
-> usize {
    let mut v___x_1703_: usize = 0;
    let mut v___x_1704_: usize = 0;
    let mut v___x_1705_: usize = 0;
    v___x_1703_ = 1usize;
    v___x_1704_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
    v___x_1705_ = lean_usize_sub(v___x_1704_, v___x_1703_);
    return v___x_1705_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1706_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_x_1708_: usize,
    mut v_x_1709_: usize,
    mut v_x_1710_: *mut leanh::LeanObject,
    mut v_x_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: usize = 0;
    let mut v___x_1714_: usize = 0;
    let mut v___x_1715_: usize = 0;
    let mut v___x_1716_: usize = 0;
    let mut v_j_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v_v_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_node_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1756_: u8 = 0;
    let mut v_unused_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1767_: u8 = 0;
    let mut v_ks_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: u8 = 0;
    let mut v_reuseFailAlloc_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1707_) == 0 {
                    v_es_1712_ = leanh::lean_ctor_get(v_x_1707_, 0);
                    v___x_1713_ = 5usize;
                    v___x_1714_ = 1usize;
                    v___x_1715_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1);
                    v___x_1716_ = lean_usize_land(v_x_1708_, v___x_1715_);
                    v_j_1717_ = lean_usize_to_nat(v___x_1716_);
                    v___x_1718_ = lean_array_get_size(v_es_1712_);
                    v___x_1719_ = lean_nat_dec_lt(v_j_1717_, v___x_1718_);
                    if v___x_1719_ == 0 {
                        leanh::lean_dec(v_j_1717_);
                        leanh::lean_dec(v_x_1711_);
                        leanh::lean_dec(v_x_1710_);
                        return v_x_1707_;
                    } else {
                        leanh::lean_inc_ref(v_es_1712_);
                        v_isSharedCheck_1756_ = (!leanh::lean_is_exclusive(v_x_1707_)) as u8;
                        if v_isSharedCheck_1756_ == 0 {
                            v_unused_1757_ = leanh::lean_ctor_get(v_x_1707_, 0);
                            leanh::lean_dec(v_unused_1757_);
                            v___x_1721_ = v_x_1707_;
                            v_isShared_1722_ = v_isSharedCheck_1756_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1707_);
                            v___x_1721_ = leanh::lean_box(0);
                            v_isShared_1722_ = v_isSharedCheck_1756_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1758_ = leanh::lean_ctor_get(v_x_1707_, 0);
                    v_vs_1759_ = leanh::lean_ctor_get(v_x_1707_, 1);
                    v_isSharedCheck_1779_ = (!leanh::lean_is_exclusive(v_x_1707_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v___x_1761_ = v_x_1707_;
                        v_isShared_1762_ = v_isSharedCheck_1779_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1759_);
                        leanh::lean_inc(v_ks_1758_);
                        leanh::lean_dec(v_x_1707_);
                        v___x_1761_ = leanh::lean_box(0);
                        v_isShared_1762_ = v_isSharedCheck_1779_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1723_ = lean_array_fget(v_es_1712_, v_j_1717_);
                v___x_1724_ = leanh::lean_box(0);
                v_xs_x27_1725_ = lean_array_fset(v_es_1712_, v_j_1717_, v___x_1724_);
                match leanh::lean_obj_tag(v_v_1723_) {
                    0 => {
                        v_key_1732_ = leanh::lean_ctor_get(v_v_1723_, 0);
                        v_val_1733_ = leanh::lean_ctor_get(v_v_1723_, 1);
                        v_isSharedCheck_1743_ = (!leanh::lean_is_exclusive(v_v_1723_)) as u8;
                        if v_isSharedCheck_1743_ == 0 {
                            v___x_1735_ = v_v_1723_;
                            v_isShared_1736_ = v_isSharedCheck_1743_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1733_);
                            leanh::lean_inc(v_key_1732_);
                            leanh::lean_dec(v_v_1723_);
                            v___x_1735_ = leanh::lean_box(0);
                            v_isShared_1736_ = v_isSharedCheck_1743_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1744_ = leanh::lean_ctor_get(v_v_1723_, 0);
                        v_isSharedCheck_1754_ = (!leanh::lean_is_exclusive(v_v_1723_)) as u8;
                        if v_isSharedCheck_1754_ == 0 {
                            v___x_1746_ = v_v_1723_;
                            v_isShared_1747_ = v_isSharedCheck_1754_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1744_);
                            leanh::lean_dec(v_v_1723_);
                            v___x_1746_ = leanh::lean_box(0);
                            v_isShared_1747_ = v_isSharedCheck_1754_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1755_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1755_, 0, v_x_1710_);
                        leanh::lean_ctor_set(v___x_1755_, 1, v_x_1711_);
                        v___y_1727_ = v___x_1755_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1728_ = lean_array_fset(v_xs_x27_1725_, v_j_1717_, v___y_1727_);
                leanh::lean_dec(v_j_1717_);
                if v_isShared_1722_ == 0 {
                    leanh::lean_ctor_set(v___x_1721_, 0, v___x_1728_);
                    v___x_1730_ = v___x_1721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1730_;
            }
            4 => {
                v___x_1737_ = l_Lean_instBEqMVarId_beq(v_x_1710_, v_key_1732_);
                if v___x_1737_ == 0 {
                    leanh::lean_del_object(v___x_1735_);
                    v___x_1738_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1732_,
                        v_val_1733_,
                        v_x_1710_,
                        v_x_1711_,
                    );
                    v___x_1739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1739_, 0, v___x_1738_);
                    v___y_1727_ = v___x_1739_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1733_);
                    leanh::lean_dec(v_key_1732_);
                    if v_isShared_1736_ == 0 {
                        leanh::lean_ctor_set(v___x_1735_, 1, v_x_1711_);
                        leanh::lean_ctor_set(v___x_1735_, 0, v_x_1710_);
                        v___x_1741_ = v___x_1735_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_x_1710_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_x_1711_);
                        v___x_1741_ = v_reuseFailAlloc_1742_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1727_ = v___x_1741_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1748_ = lean_usize_shift_right(v_x_1708_, v___x_1713_);
                v___x_1749_ = lean_usize_add(v_x_1709_, v___x_1714_);
                v___x_1750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_1744_, v___x_1748_, v___x_1749_, v_x_1710_, v_x_1711_);
                if v_isShared_1747_ == 0 {
                    leanh::lean_ctor_set(v___x_1746_, 0, v___x_1750_);
                    v___x_1752_ = v___x_1746_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1727_ = v___x_1752_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1762_ == 0 {
                    v___x_1764_ = v___x_1761_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_ks_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_vs_1759_);
                    v___x_1764_ = v_reuseFailAlloc_1778_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1765_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_1764_, v_x_1710_, v_x_1711_);
                v___x_1773_ = 7usize;
                v___x_1774_ = lean_usize_dec_le(v___x_1773_, v_x_1709_);
                if v___x_1774_ == 0 {
                    v___x_1775_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1765_);
                    v___x_1776_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1777_ = lean_nat_dec_lt(v___x_1775_, v___x_1776_);
                    leanh::lean_dec(v___x_1775_);
                    v___y_1767_ = v___x_1777_;
                    state = 10;
                    continue;
                } else {
                    v___y_1767_ = v___x_1774_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1767_ == 0 {
                    v_ks_1768_ = leanh::lean_ctor_get(v_newNode_1765_, 0);
                    leanh::lean_inc_ref(v_ks_1768_);
                    v_vs_1769_ = leanh::lean_ctor_get(v_newNode_1765_, 1);
                    leanh::lean_inc_ref(v_vs_1769_);
                    leanh::lean_dec_ref(v_newNode_1765_);
                    v___x_1770_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1771_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2);
                    v___x_1772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_1709_, v_ks_1768_, v_vs_1769_, v___x_1770_, v___x_1771_);
                    leanh::lean_dec_ref(v_vs_1769_);
                    leanh::lean_dec_ref(v_ks_1768_);
                    return v___x_1772_;
                } else {
                    return v_newNode_1765_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(
    mut v_depth_1780_: usize,
    mut v_keys_1781_: *mut leanh::LeanObject,
    mut v_vals_1782_: *mut leanh::LeanObject,
    mut v_i_1783_: *mut leanh::LeanObject,
    mut v_entries_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v_k_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u64 = 0;
    let mut v_h_1790_: usize = 0;
    let mut v___x_1791_: usize = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: usize = 0;
    let mut v___x_1794_: usize = 0;
    let mut v___x_1795_: usize = 0;
    let mut v_h_1796_: usize = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1785_ = lean_array_get_size(v_keys_1781_);
                v___x_1786_ = lean_nat_dec_lt(v_i_1783_, v___x_1785_);
                if v___x_1786_ == 0 {
                    leanh::lean_dec(v_i_1783_);
                    return v_entries_1784_;
                } else {
                    v_k_1787_ = lean_array_fget_borrowed(v_keys_1781_, v_i_1783_);
                    v_v_1788_ = lean_array_fget_borrowed(v_vals_1782_, v_i_1783_);
                    v___x_1789_ = l_Lean_instHashableMVarId_hash(v_k_1787_);
                    v_h_1790_ = lean_uint64_to_usize(v___x_1789_);
                    v___x_1791_ = 5usize;
                    v___x_1792_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1793_ = 1usize;
                    v___x_1794_ = lean_usize_sub(v_depth_1780_, v___x_1793_);
                    v___x_1795_ = lean_usize_mul(v___x_1791_, v___x_1794_);
                    v_h_1796_ = lean_usize_shift_right(v_h_1790_, v___x_1795_);
                    v___x_1797_ = lean_nat_add(v_i_1783_, v___x_1792_);
                    leanh::lean_dec(v_i_1783_);
                    leanh::lean_inc(v_v_1788_);
                    leanh::lean_inc(v_k_1787_);
                    v___x_1798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_1784_, v_h_1796_, v_depth_1780_, v_k_1787_, v_v_1788_);
                    v_i_1783_ = v___x_1797_;
                    v_entries_1784_ = v___x_1798_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(
    mut v_depth_1800_: *mut leanh::LeanObject,
    mut v_keys_1801_: *mut leanh::LeanObject,
    mut v_vals_1802_: *mut leanh::LeanObject,
    mut v_i_1803_: *mut leanh::LeanObject,
    mut v_entries_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1805_: usize = 0;
    let mut v_res_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1805_ = leanh::lean_unbox_usize(v_depth_1800_);
    leanh::lean_dec(v_depth_1800_);
    v_res_1806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_1805_, v_keys_1801_, v_vals_1802_, v_i_1803_, v_entries_1804_);
    leanh::lean_dec_ref(v_vals_1802_);
    leanh::lean_dec_ref(v_keys_1801_);
    return v_res_1806_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(
    mut v_x_1807_: *mut leanh::LeanObject,
    mut v_x_1808_: *mut leanh::LeanObject,
    mut v_x_1809_: *mut leanh::LeanObject,
    mut v_x_1810_: *mut leanh::LeanObject,
    mut v_x_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_8841__boxed_1812_: usize = 0;
    let mut v_x_8842__boxed_1813_: usize = 0;
    let mut v_res_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8841__boxed_1812_ = leanh::lean_unbox_usize(v_x_1808_);
    leanh::lean_dec(v_x_1808_);
    v_x_8842__boxed_1813_ = leanh::lean_unbox_usize(v_x_1809_);
    leanh::lean_dec(v_x_1809_);
    v_res_1814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1807_, v_x_8841__boxed_1812_, v_x_8842__boxed_1813_, v_x_1810_, v_x_1811_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(
    mut v_x_1815_: *mut leanh::LeanObject,
    mut v_x_1816_: *mut leanh::LeanObject,
    mut v_x_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1818_: u64 = 0;
    let mut v___x_1819_: usize = 0;
    let mut v___x_1820_: usize = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Lean_instHashableMVarId_hash(v_x_1816_);
    v___x_1819_ = lean_uint64_to_usize(v___x_1818_);
    v___x_1820_ = 1usize;
    v___x_1821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1815_, v___x_1819_, v___x_1820_, v_x_1816_, v_x_1817_);
    return v___x_1821_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(
    mut v_mvarId_1822_: *mut leanh::LeanObject,
    mut v_val_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v_depth_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1826_ = lean_st_ref_take(v___y_1824_);
                v_mctx_1827_ = leanh::lean_ctor_get(v___x_1826_, 0);
                v_cache_1828_ = leanh::lean_ctor_get(v___x_1826_, 1);
                v_zetaDeltaFVarIds_1829_ = leanh::lean_ctor_get(v___x_1826_, 2);
                v_postponed_1830_ = leanh::lean_ctor_get(v___x_1826_, 3);
                v_diag_1831_ = leanh::lean_ctor_get(v___x_1826_, 4);
                v_isSharedCheck_1859_ = (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                if v_isSharedCheck_1859_ == 0 {
                    v___x_1833_ = v___x_1826_;
                    v_isShared_1834_ = v_isSharedCheck_1859_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1831_);
                    leanh::lean_inc(v_postponed_1830_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1829_);
                    leanh::lean_inc(v_cache_1828_);
                    leanh::lean_inc(v_mctx_1827_);
                    leanh::lean_dec(v___x_1826_);
                    v___x_1833_ = leanh::lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1835_ = leanh::lean_ctor_get(v_mctx_1827_, 0);
                v_levelAssignDepth_1836_ = leanh::lean_ctor_get(v_mctx_1827_, 1);
                v_lmvarCounter_1837_ = leanh::lean_ctor_get(v_mctx_1827_, 2);
                v_mvarCounter_1838_ = leanh::lean_ctor_get(v_mctx_1827_, 3);
                v_lDecls_1839_ = leanh::lean_ctor_get(v_mctx_1827_, 4);
                v_decls_1840_ = leanh::lean_ctor_get(v_mctx_1827_, 5);
                v_userNames_1841_ = leanh::lean_ctor_get(v_mctx_1827_, 6);
                v_lAssignment_1842_ = leanh::lean_ctor_get(v_mctx_1827_, 7);
                v_eAssignment_1843_ = leanh::lean_ctor_get(v_mctx_1827_, 8);
                v_dAssignment_1844_ = leanh::lean_ctor_get(v_mctx_1827_, 9);
                v_isSharedCheck_1858_ = (!leanh::lean_is_exclusive(v_mctx_1827_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v___x_1846_ = v_mctx_1827_;
                    v_isShared_1847_ = v_isSharedCheck_1858_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1844_);
                    leanh::lean_inc(v_eAssignment_1843_);
                    leanh::lean_inc(v_lAssignment_1842_);
                    leanh::lean_inc(v_userNames_1841_);
                    leanh::lean_inc(v_decls_1840_);
                    leanh::lean_inc(v_lDecls_1839_);
                    leanh::lean_inc(v_mvarCounter_1838_);
                    leanh::lean_inc(v_lmvarCounter_1837_);
                    leanh::lean_inc(v_levelAssignDepth_1836_);
                    leanh::lean_inc(v_depth_1835_);
                    leanh::lean_dec(v_mctx_1827_);
                    v___x_1846_ = leanh::lean_box(0);
                    v_isShared_1847_ = v_isSharedCheck_1858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1848_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_1843_, v_mvarId_1822_, v_val_1823_);
                if v_isShared_1847_ == 0 {
                    leanh::lean_ctor_set(v___x_1846_, 8, v___x_1848_);
                    v___x_1850_ = v___x_1846_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_depth_1835_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1857_,
                        1,
                        v_levelAssignDepth_1836_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_lmvarCounter_1837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_mvarCounter_1838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_lDecls_1839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 5, v_decls_1840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 6, v_userNames_1841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 7, v_lAssignment_1842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 8, v___x_1848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 9, v_dAssignment_1844_);
                    v___x_1850_ = v_reuseFailAlloc_1857_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1834_ == 0 {
                    leanh::lean_ctor_set(v___x_1833_, 0, v___x_1850_);
                    v___x_1852_ = v___x_1833_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1856_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_cache_1828_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1856_,
                        2,
                        v_zetaDeltaFVarIds_1829_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_postponed_1830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_diag_1831_);
                    v___x_1852_ = v_reuseFailAlloc_1856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1853_ = lean_st_ref_set(v___y_1824_, v___x_1852_);
                v___x_1854_ = leanh::lean_box(0);
                v___x_1855_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                return v___x_1855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(
    mut v_mvarId_1860_: *mut leanh::LeanObject,
    mut v_val_1861_: *mut leanh::LeanObject,
    mut v___y_1862_: *mut leanh::LeanObject,
    mut v___y_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1864_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(
        v_mvarId_1860_,
        v_val_1861_,
        v___y_1862_,
    );
    leanh::lean_dec(v___y_1862_);
    return v_res_1864_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2;
    v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
    return v___x_1870_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4;
    v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
    return v___x_1873_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6;
    v___x_1876_ = l_Lean_stringToMessageData(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(
    mut v_fvarId_1877_: *mut leanh::LeanObject,
    mut v_mvarId_1878_: *mut leanh::LeanObject,
    mut v_as_1879_: *mut leanh::LeanObject,
    mut v_i_1880_: usize,
    mut v_stop_1881_: usize,
    mut v_b_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: usize = 0;
    let mut v___x_1891_: usize = 0;
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1893_ = lean_usize_dec_eq(v_i_1880_, v_stop_1881_);
                if v___x_1893_ == 0 {
                    v___x_1894_ = lean_array_uget(v_as_1879_, v_i_1880_);
                    if leanh::lean_obj_tag(v___x_1894_) == 0 {
                        v___x_1895_ = leanh::lean_box(0);
                        v_a_1889_ = v___x_1895_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1896_ = leanh::lean_ctor_get(v___x_1894_, 0);
                        v_isSharedCheck_1933_ =
                            (!leanh::lean_is_exclusive(v___x_1894_)) as u8;
                        if v_isSharedCheck_1933_ == 0 {
                            v___x_1898_ = v___x_1894_;
                            v_isShared_1899_ = v_isSharedCheck_1933_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1896_);
                            leanh::lean_dec(v___x_1894_);
                            v___x_1898_ = leanh::lean_box(0);
                            v_isShared_1899_ = v_isSharedCheck_1933_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1878_);
                    leanh::lean_dec(v_fvarId_1877_);
                    v___x_1934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1934_, 0, v_b_1882_);
                    return v___x_1934_;
                }
            }
            1 => {
                v___x_1890_ = 1usize;
                v___x_1891_ = lean_usize_add(v_i_1880_, v___x_1890_);
                v_i_1880_ = v___x_1891_;
                v_b_1882_ = v_a_1889_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1900_ = l_Lean_LocalDecl_fvarId(v_val_1896_);
                v___x_1901_ = l_Lean_instBEqFVarId_beq(v___x_1900_, v_fvarId_1877_);
                leanh::lean_dec(v___x_1900_);
                if v___x_1901_ == 0 {
                    v___x_1902_ = 1;
                    leanh::lean_inc(v_fvarId_1877_);
                    leanh::lean_inc(v_val_1896_);
                    v___x_1903_ =
                        l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(
                            v_val_1896_,
                            v_fvarId_1877_,
                            v___x_1902_,
                            v___y_1884_,
                        );
                    if leanh::lean_obj_tag(v___x_1903_) == 0 {
                        v_a_1904_ = leanh::lean_ctor_get(v___x_1903_, 0);
                        leanh::lean_inc(v_a_1904_);
                        leanh::lean_dec_ref_known(v___x_1903_, 1);
                        v___x_1905_ = (leanh::lean_unbox(v_a_1904_) as u8);
                        leanh::lean_dec(v_a_1904_);
                        if v___x_1905_ == 0 {
                            leanh::lean_del_object(v___x_1898_);
                            leanh::lean_dec(v_val_1896_);
                            v___x_1906_ = leanh::lean_box(0);
                            v_a_1889_ = v___x_1906_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1;
                            v___x_1908_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
                            v___x_1909_ = l_Lean_LocalDecl_toExpr(v_val_1896_);
                            v___x_1910_ = l_Lean_MessageData_ofExpr(v___x_1909_);
                            v___x_1911_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1911_, 0, v___x_1908_);
                            leanh::lean_ctor_set(v___x_1911_, 1, v___x_1910_);
                            v___x_1912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
                            v___x_1913_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1913_, 0, v___x_1911_);
                            leanh::lean_ctor_set(v___x_1913_, 1, v___x_1912_);
                            leanh::lean_inc(v_fvarId_1877_);
                            v___x_1914_ = l_Lean_mkFVar(v_fvarId_1877_);
                            v___x_1915_ = l_Lean_MessageData_ofExpr(v___x_1914_);
                            v___x_1916_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1916_, 0, v___x_1913_);
                            leanh::lean_ctor_set(v___x_1916_, 1, v___x_1915_);
                            v___x_1917_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
                            v___x_1918_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1918_, 0, v___x_1916_);
                            leanh::lean_ctor_set(v___x_1918_, 1, v___x_1917_);
                            if v_isShared_1899_ == 0 {
                                leanh::lean_ctor_set(v___x_1898_, 0, v___x_1918_);
                                v___x_1920_ = v___x_1898_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1923_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1918_);
                                v___x_1920_ = v_reuseFailAlloc_1923_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_1898_);
                        leanh::lean_dec(v_val_1896_);
                        leanh::lean_dec(v_mvarId_1878_);
                        leanh::lean_dec(v_fvarId_1877_);
                        v_a_1924_ = leanh::lean_ctor_get(v___x_1903_, 0);
                        v_isSharedCheck_1931_ =
                            (!leanh::lean_is_exclusive(v___x_1903_)) as u8;
                        if v_isSharedCheck_1931_ == 0 {
                            v___x_1926_ = v___x_1903_;
                            v_isShared_1927_ = v_isSharedCheck_1931_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1924_);
                            leanh::lean_dec(v___x_1903_);
                            v___x_1926_ = leanh::lean_box(0);
                            v_isShared_1927_ = v_isSharedCheck_1931_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1898_);
                    leanh::lean_dec(v_val_1896_);
                    v___x_1932_ = leanh::lean_box(0);
                    v_a_1889_ = v___x_1932_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_mvarId_1878_);
                v___x_1921_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1907_,
                    v_mvarId_1878_,
                    v___x_1920_,
                    v___y_1883_,
                    v___y_1884_,
                    v___y_1885_,
                    v___y_1886_,
                );
                if leanh::lean_obj_tag(v___x_1921_) == 0 {
                    v_a_1922_ = leanh::lean_ctor_get(v___x_1921_, 0);
                    leanh::lean_inc(v_a_1922_);
                    leanh::lean_dec_ref_known(v___x_1921_, 1);
                    v_a_1889_ = v_a_1922_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_mvarId_1878_);
                    leanh::lean_dec(v_fvarId_1877_);
                    return v___x_1921_;
                }
            }
            4 => {
                if v_isShared_1927_ == 0 {
                    v___x_1929_ = v___x_1926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
                    v___x_1929_ = v_reuseFailAlloc_1930_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(
    mut v_fvarId_1935_: *mut leanh::LeanObject,
    mut v_mvarId_1936_: *mut leanh::LeanObject,
    mut v_as_1937_: *mut leanh::LeanObject,
    mut v_i_1938_: *mut leanh::LeanObject,
    mut v_stop_1939_: *mut leanh::LeanObject,
    mut v_b_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
    mut v___y_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1946_: usize = 0;
    let mut v_stop_boxed_1947_: usize = 0;
    let mut v_res_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1946_ = leanh::lean_unbox_usize(v_i_1938_);
    leanh::lean_dec(v_i_1938_);
    v_stop_boxed_1947_ = leanh::lean_unbox_usize(v_stop_1939_);
    leanh::lean_dec(v_stop_1939_);
    v_res_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_1935_, v_mvarId_1936_, v_as_1937_, v_i_boxed_1946_, v_stop_boxed_1947_, v_b_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
    leanh::lean_dec(v___y_1944_);
    leanh::lean_dec_ref(v___y_1943_);
    leanh::lean_dec(v___y_1942_);
    leanh::lean_dec_ref(v___y_1941_);
    leanh::lean_dec_ref(v_as_1937_);
    return v_res_1948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(
    mut v_fvarId_1949_: *mut leanh::LeanObject,
    mut v_mvarId_1950_: *mut leanh::LeanObject,
    mut v_as_1951_: *mut leanh::LeanObject,
    mut v_i_1952_: usize,
    mut v_stop_1953_: usize,
    mut v_b_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1965_ = lean_usize_dec_eq(v_i_1952_, v_stop_1953_);
                if v___x_1965_ == 0 {
                    v___x_1966_ = lean_array_uget(v_as_1951_, v_i_1952_);
                    if leanh::lean_obj_tag(v___x_1966_) == 0 {
                        v___x_1967_ = leanh::lean_box(0);
                        v_a_1961_ = v___x_1967_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1968_ = leanh::lean_ctor_get(v___x_1966_, 0);
                        v_isSharedCheck_2005_ =
                            (!leanh::lean_is_exclusive(v___x_1966_)) as u8;
                        if v_isSharedCheck_2005_ == 0 {
                            v___x_1970_ = v___x_1966_;
                            v_isShared_1971_ = v_isSharedCheck_2005_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1968_);
                            leanh::lean_dec(v___x_1966_);
                            v___x_1970_ = leanh::lean_box(0);
                            v_isShared_1971_ = v_isSharedCheck_2005_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1950_);
                    leanh::lean_dec(v_fvarId_1949_);
                    v___x_2006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2006_, 0, v_b_1954_);
                    return v___x_2006_;
                }
            }
            1 => {
                v___x_1962_ = 1usize;
                v___x_1963_ = lean_usize_add(v_i_1952_, v___x_1962_);
                v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_1949_, v_mvarId_1950_, v_as_1951_, v___x_1963_, v_stop_1953_, v_a_1961_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
                return v___x_1964_;
            }
            2 => {
                v___x_1972_ = l_Lean_LocalDecl_fvarId(v_val_1968_);
                v___x_1973_ = l_Lean_instBEqFVarId_beq(v___x_1972_, v_fvarId_1949_);
                leanh::lean_dec(v___x_1972_);
                if v___x_1973_ == 0 {
                    v___x_1974_ = 1;
                    leanh::lean_inc(v_fvarId_1949_);
                    leanh::lean_inc(v_val_1968_);
                    v___x_1975_ =
                        l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(
                            v_val_1968_,
                            v_fvarId_1949_,
                            v___x_1974_,
                            v___y_1956_,
                        );
                    if leanh::lean_obj_tag(v___x_1975_) == 0 {
                        v_a_1976_ = leanh::lean_ctor_get(v___x_1975_, 0);
                        leanh::lean_inc(v_a_1976_);
                        leanh::lean_dec_ref_known(v___x_1975_, 1);
                        v___x_1977_ = (leanh::lean_unbox(v_a_1976_) as u8);
                        leanh::lean_dec(v_a_1976_);
                        if v___x_1977_ == 0 {
                            leanh::lean_del_object(v___x_1970_);
                            leanh::lean_dec(v_val_1968_);
                            v___x_1978_ = leanh::lean_box(0);
                            v_a_1961_ = v___x_1978_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1;
                            v___x_1980_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
                            v___x_1981_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
                            v___x_1982_ = l_Lean_MessageData_ofExpr(v___x_1981_);
                            v___x_1983_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1983_, 0, v___x_1980_);
                            leanh::lean_ctor_set(v___x_1983_, 1, v___x_1982_);
                            v___x_1984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
                            v___x_1985_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1985_, 0, v___x_1983_);
                            leanh::lean_ctor_set(v___x_1985_, 1, v___x_1984_);
                            leanh::lean_inc(v_fvarId_1949_);
                            v___x_1986_ = l_Lean_mkFVar(v_fvarId_1949_);
                            v___x_1987_ = l_Lean_MessageData_ofExpr(v___x_1986_);
                            v___x_1988_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1988_, 0, v___x_1985_);
                            leanh::lean_ctor_set(v___x_1988_, 1, v___x_1987_);
                            v___x_1989_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
                            v___x_1990_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1990_, 0, v___x_1988_);
                            leanh::lean_ctor_set(v___x_1990_, 1, v___x_1989_);
                            if v_isShared_1971_ == 0 {
                                leanh::lean_ctor_set(v___x_1970_, 0, v___x_1990_);
                                v___x_1992_ = v___x_1970_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1995_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1990_);
                                v___x_1992_ = v_reuseFailAlloc_1995_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_1970_);
                        leanh::lean_dec(v_val_1968_);
                        leanh::lean_dec(v_mvarId_1950_);
                        leanh::lean_dec(v_fvarId_1949_);
                        v_a_1996_ = leanh::lean_ctor_get(v___x_1975_, 0);
                        v_isSharedCheck_2003_ =
                            (!leanh::lean_is_exclusive(v___x_1975_)) as u8;
                        if v_isSharedCheck_2003_ == 0 {
                            v___x_1998_ = v___x_1975_;
                            v_isShared_1999_ = v_isSharedCheck_2003_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1996_);
                            leanh::lean_dec(v___x_1975_);
                            v___x_1998_ = leanh::lean_box(0);
                            v_isShared_1999_ = v_isSharedCheck_2003_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1970_);
                    leanh::lean_dec(v_val_1968_);
                    v___x_2004_ = leanh::lean_box(0);
                    v_a_1961_ = v___x_2004_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_mvarId_1950_);
                v___x_1993_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1979_,
                    v_mvarId_1950_,
                    v___x_1992_,
                    v___y_1955_,
                    v___y_1956_,
                    v___y_1957_,
                    v___y_1958_,
                );
                if leanh::lean_obj_tag(v___x_1993_) == 0 {
                    v_a_1994_ = leanh::lean_ctor_get(v___x_1993_, 0);
                    leanh::lean_inc(v_a_1994_);
                    leanh::lean_dec_ref_known(v___x_1993_, 1);
                    v_a_1961_ = v_a_1994_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_mvarId_1950_);
                    leanh::lean_dec(v_fvarId_1949_);
                    return v___x_1993_;
                }
            }
            4 => {
                if v_isShared_1999_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(
    mut v_fvarId_2007_: *mut leanh::LeanObject,
    mut v_mvarId_2008_: *mut leanh::LeanObject,
    mut v_as_2009_: *mut leanh::LeanObject,
    mut v_i_2010_: *mut leanh::LeanObject,
    mut v_stop_2011_: *mut leanh::LeanObject,
    mut v_b_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2018_: usize = 0;
    let mut v_stop_boxed_2019_: usize = 0;
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2018_ = leanh::lean_unbox_usize(v_i_2010_);
    leanh::lean_dec(v_i_2010_);
    v_stop_boxed_2019_ = leanh::lean_unbox_usize(v_stop_2011_);
    leanh::lean_dec(v_stop_2011_);
    v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2007_, v_mvarId_2008_, v_as_2009_, v_i_boxed_2018_, v_stop_boxed_2019_, v_b_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
    leanh::lean_dec(v___y_2016_);
    leanh::lean_dec_ref(v___y_2015_);
    leanh::lean_dec(v___y_2014_);
    leanh::lean_dec_ref(v___y_2013_);
    leanh::lean_dec_ref(v_as_2009_);
    return v_res_2020_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(
    mut v_fvarId_2021_: *mut leanh::LeanObject,
    mut v_mvarId_2022_: *mut leanh::LeanObject,
    mut v_x_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: usize = 0;
    let mut v___x_2045_: usize = 0;
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_vs_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: usize = 0;
    let mut v___x_2067_: usize = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: usize = 0;
    let mut v___x_2070_: usize = 0;
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2023_) == 0 {
                    v_cs_2029_ = leanh::lean_ctor_get(v_x_2023_, 0);
                    v_isSharedCheck_2050_ = (!leanh::lean_is_exclusive(v_x_2023_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2031_ = v_x_2023_;
                        v_isShared_2032_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_2029_);
                        leanh::lean_dec(v_x_2023_);
                        v___x_2031_ = leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2051_ = leanh::lean_ctor_get(v_x_2023_, 0);
                    v_isSharedCheck_2072_ = (!leanh::lean_is_exclusive(v_x_2023_)) as u8;
                    if v_isSharedCheck_2072_ == 0 {
                        v___x_2053_ = v_x_2023_;
                        v_isShared_2054_ = v_isSharedCheck_2072_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2051_);
                        leanh::lean_dec(v_x_2023_);
                        v___x_2053_ = leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2072_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2033_ = leanh::lean_unsigned_to_nat(0);
                v___x_2034_ = lean_array_get_size(v_cs_2029_);
                v___x_2035_ = leanh::lean_box(0);
                v___x_2036_ = lean_nat_dec_lt(v___x_2033_, v___x_2034_);
                if v___x_2036_ == 0 {
                    leanh::lean_dec_ref(v_cs_2029_);
                    leanh::lean_dec(v_mvarId_2022_);
                    leanh::lean_dec(v_fvarId_2021_);
                    if v_isShared_2032_ == 0 {
                        leanh::lean_ctor_set(v___x_2031_, 0, v___x_2035_);
                        v___x_2038_ = v___x_2031_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2035_);
                        v___x_2038_ = v_reuseFailAlloc_2039_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2040_ = lean_nat_dec_le(v___x_2034_, v___x_2034_);
                    if v___x_2040_ == 0 {
                        if v___x_2036_ == 0 {
                            leanh::lean_dec_ref(v_cs_2029_);
                            leanh::lean_dec(v_mvarId_2022_);
                            leanh::lean_dec(v_fvarId_2021_);
                            if v_isShared_2032_ == 0 {
                                leanh::lean_ctor_set(v___x_2031_, 0, v___x_2035_);
                                v___x_2042_ = v___x_2031_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2043_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2035_);
                                v___x_2042_ = v_reuseFailAlloc_2043_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2031_);
                            v___x_2044_ = 0usize;
                            v___x_2045_ = lean_usize_of_nat(v___x_2034_);
                            v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_2021_, v_mvarId_2022_, v_cs_2029_, v___x_2044_, v___x_2045_, v___x_2035_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
                            leanh::lean_dec_ref(v_cs_2029_);
                            return v___x_2046_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2031_);
                        v___x_2047_ = 0usize;
                        v___x_2048_ = lean_usize_of_nat(v___x_2034_);
                        v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_2021_, v_mvarId_2022_, v_cs_2029_, v___x_2047_, v___x_2048_, v___x_2035_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
                        leanh::lean_dec_ref(v_cs_2029_);
                        return v___x_2049_;
                    }
                }
            }
            2 => {
                return v___x_2038_;
            }
            3 => {
                return v___x_2042_;
            }
            4 => {
                v___x_2055_ = leanh::lean_unsigned_to_nat(0);
                v___x_2056_ = lean_array_get_size(v_vs_2051_);
                v___x_2057_ = leanh::lean_box(0);
                v___x_2058_ = lean_nat_dec_lt(v___x_2055_, v___x_2056_);
                if v___x_2058_ == 0 {
                    leanh::lean_dec_ref(v_vs_2051_);
                    leanh::lean_dec(v_mvarId_2022_);
                    leanh::lean_dec(v_fvarId_2021_);
                    if v_isShared_2054_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2053_, 0);
                        leanh::lean_ctor_set(v___x_2053_, 0, v___x_2057_);
                        v___x_2060_ = v___x_2053_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2057_);
                        v___x_2060_ = v_reuseFailAlloc_2061_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2062_ = lean_nat_dec_le(v___x_2056_, v___x_2056_);
                    if v___x_2062_ == 0 {
                        if v___x_2058_ == 0 {
                            leanh::lean_dec_ref(v_vs_2051_);
                            leanh::lean_dec(v_mvarId_2022_);
                            leanh::lean_dec(v_fvarId_2021_);
                            if v_isShared_2054_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_2053_, 0);
                                leanh::lean_ctor_set(v___x_2053_, 0, v___x_2057_);
                                v___x_2064_ = v___x_2053_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2065_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2057_);
                                v___x_2064_ = v_reuseFailAlloc_2065_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2053_);
                            v___x_2066_ = 0usize;
                            v___x_2067_ = lean_usize_of_nat(v___x_2056_);
                            v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2021_, v_mvarId_2022_, v_vs_2051_, v___x_2066_, v___x_2067_, v___x_2057_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
                            leanh::lean_dec_ref(v_vs_2051_);
                            return v___x_2068_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2053_);
                        v___x_2069_ = 0usize;
                        v___x_2070_ = lean_usize_of_nat(v___x_2056_);
                        v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2021_, v_mvarId_2022_, v_vs_2051_, v___x_2069_, v___x_2070_, v___x_2057_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
                        leanh::lean_dec_ref(v_vs_2051_);
                        return v___x_2071_;
                    }
                }
            }
            5 => {
                return v___x_2060_;
            }
            6 => {
                return v___x_2064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(
    mut v_fvarId_2073_: *mut leanh::LeanObject,
    mut v_mvarId_2074_: *mut leanh::LeanObject,
    mut v_as_2075_: *mut leanh::LeanObject,
    mut v_i_2076_: usize,
    mut v_stop_2077_: usize,
    mut v_b_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: usize = 0;
    let mut v___x_2089_: usize = 0;
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2084_ = lean_usize_dec_eq(v_i_2076_, v_stop_2077_);
                if v___x_2084_ == 0 {
                    v___x_2085_ = lean_array_uget_borrowed(v_as_2075_, v_i_2076_);
                    leanh::lean_inc(v___x_2085_);
                    leanh::lean_inc(v_mvarId_2074_);
                    leanh::lean_inc(v_fvarId_2073_);
                    v___x_2086_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_2073_, v_mvarId_2074_, v___x_2085_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                    if leanh::lean_obj_tag(v___x_2086_) == 0 {
                        v_a_2087_ = leanh::lean_ctor_get(v___x_2086_, 0);
                        leanh::lean_inc(v_a_2087_);
                        leanh::lean_dec_ref_known(v___x_2086_, 1);
                        v___x_2088_ = 1usize;
                        v___x_2089_ = lean_usize_add(v_i_2076_, v___x_2088_);
                        v_i_2076_ = v___x_2089_;
                        v_b_2078_ = v_a_2087_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_mvarId_2074_);
                        leanh::lean_dec(v_fvarId_2073_);
                        return v___x_2086_;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_2074_);
                    leanh::lean_dec(v_fvarId_2073_);
                    v___x_2091_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2091_, 0, v_b_2078_);
                    return v___x_2091_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(
    mut v_fvarId_2092_: *mut leanh::LeanObject,
    mut v_mvarId_2093_: *mut leanh::LeanObject,
    mut v_as_2094_: *mut leanh::LeanObject,
    mut v_i_2095_: *mut leanh::LeanObject,
    mut v_stop_2096_: *mut leanh::LeanObject,
    mut v_b_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
    mut v___y_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2103_: usize = 0;
    let mut v_stop_boxed_2104_: usize = 0;
    let mut v_res_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2103_ = leanh::lean_unbox_usize(v_i_2095_);
    leanh::lean_dec(v_i_2095_);
    v_stop_boxed_2104_ = leanh::lean_unbox_usize(v_stop_2096_);
    leanh::lean_dec(v_stop_2096_);
    v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_2092_, v_mvarId_2093_, v_as_2094_, v_i_boxed_2103_, v_stop_boxed_2104_, v_b_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
    leanh::lean_dec(v___y_2101_);
    leanh::lean_dec_ref(v___y_2100_);
    leanh::lean_dec(v___y_2099_);
    leanh::lean_dec_ref(v___y_2098_);
    leanh::lean_dec_ref(v_as_2094_);
    return v_res_2105_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(
    mut v_fvarId_2106_: *mut leanh::LeanObject,
    mut v_mvarId_2107_: *mut leanh::LeanObject,
    mut v_x_2108_: *mut leanh::LeanObject,
    mut v___y_2109_: *mut leanh::LeanObject,
    mut v___y_2110_: *mut leanh::LeanObject,
    mut v___y_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_2106_, v_mvarId_2107_, v_x_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
    leanh::lean_dec(v___y_2112_);
    leanh::lean_dec_ref(v___y_2111_);
    leanh::lean_dec(v___y_2110_);
    leanh::lean_dec_ref(v___y_2109_);
    return v_res_2114_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(
    mut v_fvarId_2115_: *mut leanh::LeanObject,
    mut v_mvarId_2116_: *mut leanh::LeanObject,
    mut v_t_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: usize = 0;
    let mut v___x_2141_: usize = 0;
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: usize = 0;
    let mut v___x_2144_: usize = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_unused_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2123_ = leanh::lean_ctor_get(v_t_2117_, 0);
                leanh::lean_inc_ref(v_root_2123_);
                v_tail_2124_ = leanh::lean_ctor_get(v_t_2117_, 1);
                leanh::lean_inc_ref(v_tail_2124_);
                leanh::lean_dec_ref(v_t_2117_);
                leanh::lean_inc(v_mvarId_2116_);
                leanh::lean_inc(v_fvarId_2115_);
                v___x_2125_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_2115_, v_mvarId_2116_, v_root_2123_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
                if leanh::lean_obj_tag(v___x_2125_) == 0 {
                    v_isSharedCheck_2146_ = (!leanh::lean_is_exclusive(v___x_2125_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v_unused_2147_ = leanh::lean_ctor_get(v___x_2125_, 0);
                        leanh::lean_dec(v_unused_2147_);
                        v___x_2127_ = v___x_2125_;
                        v_isShared_2128_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2125_);
                        v___x_2127_ = leanh::lean_box(0);
                        v_isShared_2128_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_tail_2124_);
                    leanh::lean_dec(v_mvarId_2116_);
                    leanh::lean_dec(v_fvarId_2115_);
                    return v___x_2125_;
                }
            }
            1 => {
                v___x_2129_ = leanh::lean_unsigned_to_nat(0);
                v___x_2130_ = lean_array_get_size(v_tail_2124_);
                v___x_2131_ = leanh::lean_box(0);
                v___x_2132_ = lean_nat_dec_lt(v___x_2129_, v___x_2130_);
                if v___x_2132_ == 0 {
                    leanh::lean_dec_ref(v_tail_2124_);
                    leanh::lean_dec(v_mvarId_2116_);
                    leanh::lean_dec(v_fvarId_2115_);
                    if v_isShared_2128_ == 0 {
                        leanh::lean_ctor_set(v___x_2127_, 0, v___x_2131_);
                        v___x_2134_ = v___x_2127_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2135_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2131_);
                        v___x_2134_ = v_reuseFailAlloc_2135_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2136_ = lean_nat_dec_le(v___x_2130_, v___x_2130_);
                    if v___x_2136_ == 0 {
                        if v___x_2132_ == 0 {
                            leanh::lean_dec_ref(v_tail_2124_);
                            leanh::lean_dec(v_mvarId_2116_);
                            leanh::lean_dec(v_fvarId_2115_);
                            if v_isShared_2128_ == 0 {
                                leanh::lean_ctor_set(v___x_2127_, 0, v___x_2131_);
                                v___x_2138_ = v___x_2127_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2139_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2131_);
                                v___x_2138_ = v_reuseFailAlloc_2139_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2127_);
                            v___x_2140_ = 0usize;
                            v___x_2141_ = lean_usize_of_nat(v___x_2130_);
                            v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2115_, v_mvarId_2116_, v_tail_2124_, v___x_2140_, v___x_2141_, v___x_2131_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
                            leanh::lean_dec_ref(v_tail_2124_);
                            return v___x_2142_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2127_);
                        v___x_2143_ = 0usize;
                        v___x_2144_ = lean_usize_of_nat(v___x_2130_);
                        v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2115_, v_mvarId_2116_, v_tail_2124_, v___x_2143_, v___x_2144_, v___x_2131_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
                        leanh::lean_dec_ref(v_tail_2124_);
                        return v___x_2145_;
                    }
                }
            }
            2 => {
                return v___x_2134_;
            }
            3 => {
                return v___x_2138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(
    mut v_fvarId_2148_: *mut leanh::LeanObject,
    mut v_mvarId_2149_: *mut leanh::LeanObject,
    mut v_t_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_2148_, v_mvarId_2149_, v_t_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
    leanh::lean_dec(v___y_2154_);
    leanh::lean_dec_ref(v___y_2153_);
    leanh::lean_dec(v___y_2152_);
    leanh::lean_dec_ref(v___y_2151_);
    return v_res_2156_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2157_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_2157_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(
    mut v_fvarId_2158_: *mut leanh::LeanObject,
    mut v_mvarId_2159_: *mut leanh::LeanObject,
    mut v_x_2160_: *mut leanh::LeanObject,
    mut v_x_2161_: usize,
    mut v_x_2162_: usize,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
    mut v___y_2165_: *mut leanh::LeanObject,
    mut v___y_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: usize = 0;
    let mut v_j_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: usize = 0;
    let mut v___x_2174_: usize = 0;
    let mut v___x_2175_: usize = 0;
    let mut v___x_2176_: usize = 0;
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: usize = 0;
    let mut v___x_2196_: usize = 0;
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: usize = 0;
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut v_unused_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: u8 = 0;
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: usize = 0;
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: usize = 0;
    let mut v___x_2222_: usize = 0;
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2160_) == 0 {
                    v_cs_2168_ = leanh::lean_ctor_get(v_x_2160_, 0);
                    leanh::lean_inc_ref(v_cs_2168_);
                    leanh::lean_dec_ref_known(v_x_2160_, 1);
                    v___x_2169_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
                    v___x_2170_ = lean_usize_shift_right(v_x_2161_, v_x_2162_);
                    v_j_2171_ = lean_usize_to_nat(v___x_2170_);
                    v___x_2172_ = lean_array_get_borrowed(v___x_2169_, v_cs_2168_, v_j_2171_);
                    v___x_2173_ = 1usize;
                    v___x_2174_ = lean_usize_shift_left(v___x_2173_, v_x_2162_);
                    v___x_2175_ = lean_usize_sub(v___x_2174_, v___x_2173_);
                    v___x_2176_ = lean_usize_land(v_x_2161_, v___x_2175_);
                    v___x_2177_ = 5usize;
                    v___x_2178_ = lean_usize_sub(v_x_2162_, v___x_2177_);
                    leanh::lean_inc(v___x_2172_);
                    leanh::lean_inc(v_mvarId_2159_);
                    leanh::lean_inc(v_fvarId_2158_);
                    v___x_2179_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_2158_, v_mvarId_2159_, v___x_2172_, v___x_2176_, v___x_2178_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
                    if leanh::lean_obj_tag(v___x_2179_) == 0 {
                        v_isSharedCheck_2201_ =
                            (!leanh::lean_is_exclusive(v___x_2179_)) as u8;
                        if v_isSharedCheck_2201_ == 0 {
                            v_unused_2202_ = leanh::lean_ctor_get(v___x_2179_, 0);
                            leanh::lean_dec(v_unused_2202_);
                            v___x_2181_ = v___x_2179_;
                            v_isShared_2182_ = v_isSharedCheck_2201_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2179_);
                            v___x_2181_ = leanh::lean_box(0);
                            v_isShared_2182_ = v_isSharedCheck_2201_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_j_2171_);
                        leanh::lean_dec_ref(v_cs_2168_);
                        leanh::lean_dec(v_mvarId_2159_);
                        leanh::lean_dec(v_fvarId_2158_);
                        return v___x_2179_;
                    }
                } else {
                    v_vs_2203_ = leanh::lean_ctor_get(v_x_2160_, 0);
                    v_isSharedCheck_2224_ = (!leanh::lean_is_exclusive(v_x_2160_)) as u8;
                    if v_isSharedCheck_2224_ == 0 {
                        v___x_2205_ = v_x_2160_;
                        v_isShared_2206_ = v_isSharedCheck_2224_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2203_);
                        leanh::lean_dec(v_x_2160_);
                        v___x_2205_ = leanh::lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2224_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2183_ = leanh::lean_unsigned_to_nat(1);
                v___x_2184_ = lean_nat_add(v_j_2171_, v___x_2183_);
                leanh::lean_dec(v_j_2171_);
                v___x_2185_ = lean_array_get_size(v_cs_2168_);
                v___x_2186_ = leanh::lean_box(0);
                v___x_2187_ = lean_nat_dec_lt(v___x_2184_, v___x_2185_);
                if v___x_2187_ == 0 {
                    leanh::lean_dec(v___x_2184_);
                    leanh::lean_dec_ref(v_cs_2168_);
                    leanh::lean_dec(v_mvarId_2159_);
                    leanh::lean_dec(v_fvarId_2158_);
                    if v_isShared_2182_ == 0 {
                        leanh::lean_ctor_set(v___x_2181_, 0, v___x_2186_);
                        v___x_2189_ = v___x_2181_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2186_);
                        v___x_2189_ = v_reuseFailAlloc_2190_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2191_ = lean_nat_dec_le(v___x_2185_, v___x_2185_);
                    if v___x_2191_ == 0 {
                        if v___x_2187_ == 0 {
                            leanh::lean_dec(v___x_2184_);
                            leanh::lean_dec_ref(v_cs_2168_);
                            leanh::lean_dec(v_mvarId_2159_);
                            leanh::lean_dec(v_fvarId_2158_);
                            if v_isShared_2182_ == 0 {
                                leanh::lean_ctor_set(v___x_2181_, 0, v___x_2186_);
                                v___x_2193_ = v___x_2181_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2194_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2186_);
                                v___x_2193_ = v_reuseFailAlloc_2194_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2181_);
                            v___x_2195_ = lean_usize_of_nat(v___x_2184_);
                            leanh::lean_dec(v___x_2184_);
                            v___x_2196_ = lean_usize_of_nat(v___x_2185_);
                            v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_2158_, v_mvarId_2159_, v_cs_2168_, v___x_2195_, v___x_2196_, v___x_2186_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
                            leanh::lean_dec_ref(v_cs_2168_);
                            return v___x_2197_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2181_);
                        v___x_2198_ = lean_usize_of_nat(v___x_2184_);
                        leanh::lean_dec(v___x_2184_);
                        v___x_2199_ = lean_usize_of_nat(v___x_2185_);
                        v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_2158_, v_mvarId_2159_, v_cs_2168_, v___x_2198_, v___x_2199_, v___x_2186_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
                        leanh::lean_dec_ref(v_cs_2168_);
                        return v___x_2200_;
                    }
                }
            }
            2 => {
                return v___x_2189_;
            }
            3 => {
                return v___x_2193_;
            }
            4 => {
                v___x_2207_ = lean_usize_to_nat(v_x_2161_);
                v___x_2208_ = lean_array_get_size(v_vs_2203_);
                v___x_2209_ = leanh::lean_box(0);
                v___x_2210_ = lean_nat_dec_lt(v___x_2207_, v___x_2208_);
                if v___x_2210_ == 0 {
                    leanh::lean_dec(v___x_2207_);
                    leanh::lean_dec_ref(v_vs_2203_);
                    leanh::lean_dec(v_mvarId_2159_);
                    leanh::lean_dec(v_fvarId_2158_);
                    if v_isShared_2206_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2205_, 0);
                        leanh::lean_ctor_set(v___x_2205_, 0, v___x_2209_);
                        v___x_2212_ = v___x_2205_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2209_);
                        v___x_2212_ = v_reuseFailAlloc_2213_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2214_ = lean_nat_dec_le(v___x_2208_, v___x_2208_);
                    if v___x_2214_ == 0 {
                        if v___x_2210_ == 0 {
                            leanh::lean_dec(v___x_2207_);
                            leanh::lean_dec_ref(v_vs_2203_);
                            leanh::lean_dec(v_mvarId_2159_);
                            leanh::lean_dec(v_fvarId_2158_);
                            if v_isShared_2206_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_2205_, 0);
                                leanh::lean_ctor_set(v___x_2205_, 0, v___x_2209_);
                                v___x_2216_ = v___x_2205_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2217_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2209_);
                                v___x_2216_ = v_reuseFailAlloc_2217_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2205_);
                            v___x_2218_ = lean_usize_of_nat(v___x_2207_);
                            leanh::lean_dec(v___x_2207_);
                            v___x_2219_ = lean_usize_of_nat(v___x_2208_);
                            v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2158_, v_mvarId_2159_, v_vs_2203_, v___x_2218_, v___x_2219_, v___x_2209_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
                            leanh::lean_dec_ref(v_vs_2203_);
                            return v___x_2220_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2205_);
                        v___x_2221_ = lean_usize_of_nat(v___x_2207_);
                        leanh::lean_dec(v___x_2207_);
                        v___x_2222_ = lean_usize_of_nat(v___x_2208_);
                        v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2158_, v_mvarId_2159_, v_vs_2203_, v___x_2221_, v___x_2222_, v___x_2209_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
                        leanh::lean_dec_ref(v_vs_2203_);
                        return v___x_2223_;
                    }
                }
            }
            5 => {
                return v___x_2212_;
            }
            6 => {
                return v___x_2216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(
    mut v_fvarId_2225_: *mut leanh::LeanObject,
    mut v_mvarId_2226_: *mut leanh::LeanObject,
    mut v_x_2227_: *mut leanh::LeanObject,
    mut v_x_2228_: *mut leanh::LeanObject,
    mut v_x_2229_: *mut leanh::LeanObject,
    mut v___y_2230_: *mut leanh::LeanObject,
    mut v___y_2231_: *mut leanh::LeanObject,
    mut v___y_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
    mut v___y_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9536__boxed_2235_: usize = 0;
    let mut v_x_9537__boxed_2236_: usize = 0;
    let mut v_res_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9536__boxed_2235_ = leanh::lean_unbox_usize(v_x_2228_);
    leanh::lean_dec(v_x_2228_);
    v_x_9537__boxed_2236_ = leanh::lean_unbox_usize(v_x_2229_);
    leanh::lean_dec(v_x_2229_);
    v_res_2237_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_2225_, v_mvarId_2226_, v_x_2227_, v_x_9536__boxed_2235_, v_x_9537__boxed_2236_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
    leanh::lean_dec(v___y_2233_);
    leanh::lean_dec_ref(v___y_2232_);
    leanh::lean_dec(v___y_2231_);
    leanh::lean_dec_ref(v___y_2230_);
    return v_res_2237_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(
    mut v_fvarId_2238_: *mut leanh::LeanObject,
    mut v_mvarId_2239_: *mut leanh::LeanObject,
    mut v_t_2240_: *mut leanh::LeanObject,
    mut v_start_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
    mut v___y_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    let mut v_root_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_2251_: usize = 0;
    let mut v_tailOff_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: usize = 0;
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: usize = 0;
    let mut v___x_2270_: usize = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: usize = 0;
    let mut v___x_2273_: usize = 0;
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_unused_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: usize = 0;
    let mut v___x_2285_: usize = 0;
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: usize = 0;
    let mut v___x_2288_: usize = 0;
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2247_ = leanh::lean_unsigned_to_nat(0);
                v___x_2248_ = lean_nat_dec_eq(v_start_2241_, v___x_2247_);
                if v___x_2248_ == 0 {
                    v_root_2249_ = leanh::lean_ctor_get(v_t_2240_, 0);
                    leanh::lean_inc_ref(v_root_2249_);
                    v_tail_2250_ = leanh::lean_ctor_get(v_t_2240_, 1);
                    leanh::lean_inc_ref(v_tail_2250_);
                    v_shift_2251_ = leanh::lean_ctor_get_usize(v_t_2240_, 4);
                    v_tailOff_2252_ = leanh::lean_ctor_get(v_t_2240_, 3);
                    leanh::lean_inc(v_tailOff_2252_);
                    leanh::lean_dec_ref(v_t_2240_);
                    v___x_2253_ = lean_nat_dec_le(v_tailOff_2252_, v_start_2241_);
                    if v___x_2253_ == 0 {
                        leanh::lean_dec(v_tailOff_2252_);
                        v___x_2254_ = lean_usize_of_nat(v_start_2241_);
                        leanh::lean_inc(v_mvarId_2239_);
                        leanh::lean_inc(v_fvarId_2238_);
                        v___x_2255_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_2238_, v_mvarId_2239_, v_root_2249_, v___x_2254_, v_shift_2251_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
                        if leanh::lean_obj_tag(v___x_2255_) == 0 {
                            v_isSharedCheck_2275_ =
                                (!leanh::lean_is_exclusive(v___x_2255_)) as u8;
                            if v_isSharedCheck_2275_ == 0 {
                                v_unused_2276_ = leanh::lean_ctor_get(v___x_2255_, 0);
                                leanh::lean_dec(v_unused_2276_);
                                v___x_2257_ = v___x_2255_;
                                v_isShared_2258_ = v_isSharedCheck_2275_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2255_);
                                v___x_2257_ = leanh::lean_box(0);
                                v_isShared_2258_ = v_isSharedCheck_2275_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_tail_2250_);
                            leanh::lean_dec(v_mvarId_2239_);
                            leanh::lean_dec(v_fvarId_2238_);
                            return v___x_2255_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_root_2249_);
                        v___x_2277_ = lean_nat_sub(v_start_2241_, v_tailOff_2252_);
                        leanh::lean_dec(v_tailOff_2252_);
                        v___x_2278_ = lean_array_get_size(v_tail_2250_);
                        v___x_2279_ = leanh::lean_box(0);
                        v___x_2280_ = lean_nat_dec_lt(v___x_2277_, v___x_2278_);
                        if v___x_2280_ == 0 {
                            leanh::lean_dec(v___x_2277_);
                            leanh::lean_dec_ref(v_tail_2250_);
                            leanh::lean_dec(v_mvarId_2239_);
                            leanh::lean_dec(v_fvarId_2238_);
                            v___x_2281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2281_, 0, v___x_2279_);
                            return v___x_2281_;
                        } else {
                            v___x_2282_ = lean_nat_dec_le(v___x_2278_, v___x_2278_);
                            if v___x_2282_ == 0 {
                                if v___x_2280_ == 0 {
                                    leanh::lean_dec(v___x_2277_);
                                    leanh::lean_dec_ref(v_tail_2250_);
                                    leanh::lean_dec(v_mvarId_2239_);
                                    leanh::lean_dec(v_fvarId_2238_);
                                    v___x_2283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2283_, 0, v___x_2279_);
                                    return v___x_2283_;
                                } else {
                                    v___x_2284_ = lean_usize_of_nat(v___x_2277_);
                                    leanh::lean_dec(v___x_2277_);
                                    v___x_2285_ = lean_usize_of_nat(v___x_2278_);
                                    v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2238_, v_mvarId_2239_, v_tail_2250_, v___x_2284_, v___x_2285_, v___x_2279_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
                                    leanh::lean_dec_ref(v_tail_2250_);
                                    return v___x_2286_;
                                }
                            } else {
                                v___x_2287_ = lean_usize_of_nat(v___x_2277_);
                                leanh::lean_dec(v___x_2277_);
                                v___x_2288_ = lean_usize_of_nat(v___x_2278_);
                                v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2238_, v_mvarId_2239_, v_tail_2250_, v___x_2287_, v___x_2288_, v___x_2279_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
                                leanh::lean_dec_ref(v_tail_2250_);
                                return v___x_2289_;
                            }
                        }
                    }
                } else {
                    v___x_2290_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_2238_, v_mvarId_2239_, v_t_2240_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
                    return v___x_2290_;
                }
            }
            1 => {
                v___x_2259_ = lean_array_get_size(v_tail_2250_);
                v___x_2260_ = leanh::lean_box(0);
                v___x_2261_ = lean_nat_dec_lt(v___x_2247_, v___x_2259_);
                if v___x_2261_ == 0 {
                    leanh::lean_dec_ref(v_tail_2250_);
                    leanh::lean_dec(v_mvarId_2239_);
                    leanh::lean_dec(v_fvarId_2238_);
                    if v_isShared_2258_ == 0 {
                        leanh::lean_ctor_set(v___x_2257_, 0, v___x_2260_);
                        v___x_2263_ = v___x_2257_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2260_);
                        v___x_2263_ = v_reuseFailAlloc_2264_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2265_ = lean_nat_dec_le(v___x_2259_, v___x_2259_);
                    if v___x_2265_ == 0 {
                        if v___x_2261_ == 0 {
                            leanh::lean_dec_ref(v_tail_2250_);
                            leanh::lean_dec(v_mvarId_2239_);
                            leanh::lean_dec(v_fvarId_2238_);
                            if v_isShared_2258_ == 0 {
                                leanh::lean_ctor_set(v___x_2257_, 0, v___x_2260_);
                                v___x_2267_ = v___x_2257_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2268_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2260_);
                                v___x_2267_ = v_reuseFailAlloc_2268_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2257_);
                            v___x_2269_ = 0usize;
                            v___x_2270_ = lean_usize_of_nat(v___x_2259_);
                            v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2238_, v_mvarId_2239_, v_tail_2250_, v___x_2269_, v___x_2270_, v___x_2260_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
                            leanh::lean_dec_ref(v_tail_2250_);
                            return v___x_2271_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2257_);
                        v___x_2272_ = 0usize;
                        v___x_2273_ = lean_usize_of_nat(v___x_2259_);
                        v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_2238_, v_mvarId_2239_, v_tail_2250_, v___x_2272_, v___x_2273_, v___x_2260_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
                        leanh::lean_dec_ref(v_tail_2250_);
                        return v___x_2274_;
                    }
                }
            }
            2 => {
                return v___x_2263_;
            }
            3 => {
                return v___x_2267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(
    mut v_fvarId_2291_: *mut leanh::LeanObject,
    mut v_mvarId_2292_: *mut leanh::LeanObject,
    mut v_t_2293_: *mut leanh::LeanObject,
    mut v_start_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_2291_, v_mvarId_2292_, v_t_2293_, v_start_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
    leanh::lean_dec(v___y_2298_);
    leanh::lean_dec_ref(v___y_2297_);
    leanh::lean_dec(v___y_2296_);
    leanh::lean_dec_ref(v___y_2295_);
    leanh::lean_dec(v_start_2294_);
    return v_res_2300_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(
    mut v_fvarId_2301_: *mut leanh::LeanObject,
    mut v_mvarId_2302_: *mut leanh::LeanObject,
    mut v_lctx_2303_: *mut leanh::LeanObject,
    mut v_start_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decls_2310_ = leanh::lean_ctor_get(v_lctx_2303_, 1);
    leanh::lean_inc_ref(v_decls_2310_);
    leanh::lean_dec_ref(v_lctx_2303_);
    v___x_2311_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_2301_, v_mvarId_2302_, v_decls_2310_, v_start_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
    return v___x_2311_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(
    mut v_fvarId_2312_: *mut leanh::LeanObject,
    mut v_mvarId_2313_: *mut leanh::LeanObject,
    mut v_lctx_2314_: *mut leanh::LeanObject,
    mut v_start_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
    mut v___y_2320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2321_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(
        v_fvarId_2312_,
        v_mvarId_2313_,
        v_lctx_2314_,
        v_start_2315_,
        v___y_2316_,
        v___y_2317_,
        v___y_2318_,
        v___y_2319_,
    );
    leanh::lean_dec(v___y_2319_);
    leanh::lean_dec_ref(v___y_2318_);
    leanh::lean_dec(v___y_2317_);
    leanh::lean_dec_ref(v___y_2316_);
    leanh::lean_dec(v_start_2315_);
    return v_res_2321_;
}
pub unsafe fn _init_l_Lean_MVarId_clear___lam__1___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = l_Lean_MVarId_clear___lam__1___closed__0;
    v___x_2324_ = l_Lean_stringToMessageData(v___x_2323_);
    return v___x_2324_;
}
pub unsafe fn _init_l_Lean_MVarId_clear___lam__1___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2326_ = l_Lean_MVarId_clear___lam__1___closed__2;
    v___x_2327_ = l_Lean_stringToMessageData(v___x_2326_);
    return v___x_2327_;
}
pub unsafe fn l_Lean_MVarId_clear___lam__1(
    mut v_mvarId_2328_: *mut leanh::LeanObject,
    mut v___x_2329_: *mut leanh::LeanObject,
    mut v_fvarId_2330_: *mut leanh::LeanObject,
    mut v___f_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v_unused_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2363_: u8 = 0;
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2367_: u8 = 0;
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v_reuseFailAlloc_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut v_a_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_a_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut v_a_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2439_: u8 = 0;
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut v_a_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_2329_);
                leanh::lean_inc(v_mvarId_2328_);
                v___x_2368_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2328_,
                    v___x_2329_,
                    v___y_2332_,
                    v___y_2333_,
                    v___y_2334_,
                    v___y_2335_,
                );
                if leanh::lean_obj_tag(v___x_2368_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2368_, 1);
                    v_lctx_2369_ = leanh::lean_ctor_get(v___y_2332_, 2);
                    leanh::lean_inc_ref(v_lctx_2369_);
                    v___x_2444_ = l_Lean_LocalContext_contains(v_lctx_2369_, v_fvarId_2330_);
                    if v___x_2444_ == 0 {
                        v___x_2445_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_clear___lam__1___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_clear___lam__1___closed__3_once),
                            _init_l_Lean_MVarId_clear___lam__1___closed__3,
                        );
                        leanh::lean_inc(v_fvarId_2330_);
                        v___x_2446_ = l_Lean_mkFVar(v_fvarId_2330_);
                        v___x_2447_ = l_Lean_MessageData_ofExpr(v___x_2446_);
                        v___x_2448_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2448_, 0, v___x_2445_);
                        leanh::lean_ctor_set(v___x_2448_, 1, v___x_2447_);
                        v___x_2449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
                        v___x_2450_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2450_, 0, v___x_2448_);
                        leanh::lean_ctor_set(v___x_2450_, 1, v___x_2449_);
                        v___x_2451_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                        leanh::lean_inc(v_mvarId_2328_);
                        leanh::lean_inc(v___x_2329_);
                        v___x_2452_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_2329_,
                            v_mvarId_2328_,
                            v___x_2451_,
                            v___y_2332_,
                            v___y_2333_,
                            v___y_2334_,
                            v___y_2335_,
                        );
                        if leanh::lean_obj_tag(v___x_2452_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2452_, 1);
                            v___y_2384_ = v___y_2332_;
                            v___y_2385_ = v___y_2333_;
                            v___y_2386_ = v___y_2334_;
                            v___y_2387_ = v___y_2335_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_lctx_2369_);
                            leanh::lean_dec_ref(v___y_2332_);
                            leanh::lean_dec_ref(v___f_2331_);
                            leanh::lean_dec(v_fvarId_2330_);
                            leanh::lean_dec(v___x_2329_);
                            leanh::lean_dec(v_mvarId_2328_);
                            v_a_2453_ = leanh::lean_ctor_get(v___x_2452_, 0);
                            v_isSharedCheck_2460_ =
                                (!leanh::lean_is_exclusive(v___x_2452_)) as u8;
                            if v_isSharedCheck_2460_ == 0 {
                                v___x_2455_ = v___x_2452_;
                                v_isShared_2456_ = v_isSharedCheck_2460_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2453_);
                                leanh::lean_dec(v___x_2452_);
                                v___x_2455_ = leanh::lean_box(0);
                                v_isShared_2456_ = v_isSharedCheck_2460_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        v___y_2384_ = v___y_2332_;
                        v___y_2385_ = v___y_2333_;
                        v___y_2386_ = v___y_2334_;
                        v___y_2387_ = v___y_2335_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2332_);
                    leanh::lean_dec_ref(v___f_2331_);
                    leanh::lean_dec(v_fvarId_2330_);
                    leanh::lean_dec(v___x_2329_);
                    leanh::lean_dec(v_mvarId_2328_);
                    v_a_2461_ = leanh::lean_ctor_get(v___x_2368_, 0);
                    v_isSharedCheck_2468_ = (!leanh::lean_is_exclusive(v___x_2368_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2463_ = v___x_2368_;
                        v_isShared_2464_ = v_isSharedCheck_2468_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2461_);
                        leanh::lean_dec(v___x_2368_);
                        v___x_2463_ = leanh::lean_box(0);
                        v_isShared_2464_ = v_isSharedCheck_2468_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2347_ = 2;
                v___x_2348_ = l_Lean_Meta_mkFreshExprMVarAt(
                    v___y_2340_,
                    v___y_2346_,
                    v___y_2343_,
                    v___x_2347_,
                    v___y_2342_,
                    v___y_2341_,
                    v___y_2338_,
                    v___y_2339_,
                    v___y_2345_,
                    v___y_2344_,
                );
                leanh::lean_dec_ref(v___y_2338_);
                if leanh::lean_obj_tag(v___x_2348_) == 0 {
                    v_a_2349_ = leanh::lean_ctor_get(v___x_2348_, 0);
                    leanh::lean_inc_n(v_a_2349_, 2);
                    leanh::lean_dec_ref_known(v___x_2348_, 1);
                    v___x_2350_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(
                        v_mvarId_2328_,
                        v_a_2349_,
                        v___y_2339_,
                    );
                    v_isSharedCheck_2358_ = (!leanh::lean_is_exclusive(v___x_2350_)) as u8;
                    if v_isSharedCheck_2358_ == 0 {
                        v_unused_2359_ = leanh::lean_ctor_get(v___x_2350_, 0);
                        leanh::lean_dec(v_unused_2359_);
                        v___x_2352_ = v___x_2350_;
                        v_isShared_2353_ = v_isSharedCheck_2358_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2350_);
                        v___x_2352_ = leanh::lean_box(0);
                        v_isShared_2353_ = v_isSharedCheck_2358_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_2328_);
                    v_a_2360_ = leanh::lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2367_ = (!leanh::lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2367_ == 0 {
                        v___x_2362_ = v___x_2348_;
                        v_isShared_2363_ = v_isSharedCheck_2367_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2360_);
                        leanh::lean_dec(v___x_2348_);
                        v___x_2362_ = leanh::lean_box(0);
                        v_isShared_2363_ = v_isSharedCheck_2367_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2354_ = l_Lean_Expr_mvarId_x21(v_a_2349_);
                leanh::lean_dec(v_a_2349_);
                if v_isShared_2353_ == 0 {
                    leanh::lean_ctor_set(v___x_2352_, 0, v___x_2354_);
                    v___x_2356_ = v___x_2352_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2356_;
            }
            4 => {
                if v_isShared_2363_ == 0 {
                    v___x_2365_ = v___x_2362_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2366_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
                    v___x_2365_ = v_reuseFailAlloc_2366_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2365_;
            }
            6 => {
                v_localInstances_2378_ = leanh::lean_ctor_get(v___y_2374_, 3);
                v___x_2379_ = lean_local_ctx_erase(v_lctx_2369_, v_fvarId_2330_);
                leanh::lean_inc(v___y_2371_);
                v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
                    leanh::lean_box(0),
                    v___f_2331_,
                    v_localInstances_2378_,
                    v___y_2371_,
                );
                if leanh::lean_obj_tag(v___x_2380_) == 0 {
                    leanh::lean_inc_ref(v_localInstances_2378_);
                    v___y_2338_ = v___y_2374_;
                    v___y_2339_ = v___y_2375_;
                    v___y_2340_ = v___x_2379_;
                    v___y_2341_ = v___y_2371_;
                    v___y_2342_ = v___y_2372_;
                    v___y_2343_ = v___y_2373_;
                    v___y_2344_ = v___y_2377_;
                    v___y_2345_ = v___y_2376_;
                    v___y_2346_ = v_localInstances_2378_;
                    state = 1;
                    continue;
                } else {
                    v_val_2381_ = leanh::lean_ctor_get(v___x_2380_, 0);
                    leanh::lean_inc(v_val_2381_);
                    leanh::lean_dec_ref_known(v___x_2380_, 1);
                    leanh::lean_inc_ref(v_localInstances_2378_);
                    v___x_2382_ = l_Array_eraseIdx___redArg(v_localInstances_2378_, v_val_2381_);
                    v___y_2338_ = v___y_2374_;
                    v___y_2339_ = v___y_2375_;
                    v___y_2340_ = v___x_2379_;
                    v___y_2341_ = v___y_2371_;
                    v___y_2342_ = v___y_2372_;
                    v___y_2343_ = v___y_2373_;
                    v___y_2344_ = v___y_2377_;
                    v___y_2345_ = v___y_2376_;
                    v___y_2346_ = v___x_2382_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v_mvarId_2328_);
                v___x_2388_ = l_Lean_MVarId_getTag(
                    v_mvarId_2328_,
                    v___y_2384_,
                    v___y_2385_,
                    v___y_2386_,
                    v___y_2387_,
                );
                if leanh::lean_obj_tag(v___x_2388_) == 0 {
                    v_a_2389_ = leanh::lean_ctor_get(v___x_2388_, 0);
                    leanh::lean_inc(v_a_2389_);
                    leanh::lean_dec_ref_known(v___x_2388_, 1);
                    v___x_2390_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc_ref(v_lctx_2369_);
                    leanh::lean_inc(v_mvarId_2328_);
                    leanh::lean_inc(v_fvarId_2330_);
                    v___x_2391_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(
                        v_fvarId_2330_,
                        v_mvarId_2328_,
                        v_lctx_2369_,
                        v___x_2390_,
                        v___y_2384_,
                        v___y_2385_,
                        v___y_2386_,
                        v___y_2387_,
                    );
                    if leanh::lean_obj_tag(v___x_2391_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2391_, 1);
                        leanh::lean_inc(v_mvarId_2328_);
                        v___x_2392_ = l_Lean_MVarId_getDecl(
                            v_mvarId_2328_,
                            v___y_2384_,
                            v___y_2385_,
                            v___y_2386_,
                            v___y_2387_,
                        );
                        if leanh::lean_obj_tag(v___x_2392_) == 0 {
                            v_a_2393_ = leanh::lean_ctor_get(v___x_2392_, 0);
                            leanh::lean_inc(v_a_2393_);
                            leanh::lean_dec_ref_known(v___x_2392_, 1);
                            v_type_2394_ = leanh::lean_ctor_get(v_a_2393_, 2);
                            leanh::lean_inc_ref_n(v_type_2394_, 2);
                            leanh::lean_dec(v_a_2393_);
                            leanh::lean_inc(v_fvarId_2330_);
                            v___x_2395_ =
                                l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(
                                    v_type_2394_,
                                    v_fvarId_2330_,
                                    v___y_2385_,
                                );
                            v_a_2396_ = leanh::lean_ctor_get(v___x_2395_, 0);
                            v_isSharedCheck_2419_ =
                                (!leanh::lean_is_exclusive(v___x_2395_)) as u8;
                            if v_isSharedCheck_2419_ == 0 {
                                v___x_2398_ = v___x_2395_;
                                v_isShared_2399_ = v_isSharedCheck_2419_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2396_);
                                leanh::lean_dec(v___x_2395_);
                                v___x_2398_ = leanh::lean_box(0);
                                v_isShared_2399_ = v_isSharedCheck_2419_;
                                state = 8;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2389_);
                            leanh::lean_dec_ref(v___y_2384_);
                            leanh::lean_dec_ref(v_lctx_2369_);
                            leanh::lean_dec_ref(v___f_2331_);
                            leanh::lean_dec(v_fvarId_2330_);
                            leanh::lean_dec(v___x_2329_);
                            leanh::lean_dec(v_mvarId_2328_);
                            v_a_2420_ = leanh::lean_ctor_get(v___x_2392_, 0);
                            v_isSharedCheck_2427_ =
                                (!leanh::lean_is_exclusive(v___x_2392_)) as u8;
                            if v_isSharedCheck_2427_ == 0 {
                                v___x_2422_ = v___x_2392_;
                                v_isShared_2423_ = v_isSharedCheck_2427_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2420_);
                                leanh::lean_dec(v___x_2392_);
                                v___x_2422_ = leanh::lean_box(0);
                                v_isShared_2423_ = v_isSharedCheck_2427_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2389_);
                        leanh::lean_dec_ref(v___y_2384_);
                        leanh::lean_dec_ref(v_lctx_2369_);
                        leanh::lean_dec_ref(v___f_2331_);
                        leanh::lean_dec(v_fvarId_2330_);
                        leanh::lean_dec(v___x_2329_);
                        leanh::lean_dec(v_mvarId_2328_);
                        v_a_2428_ = leanh::lean_ctor_get(v___x_2391_, 0);
                        v_isSharedCheck_2435_ =
                            (!leanh::lean_is_exclusive(v___x_2391_)) as u8;
                        if v_isSharedCheck_2435_ == 0 {
                            v___x_2430_ = v___x_2391_;
                            v_isShared_2431_ = v_isSharedCheck_2435_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2428_);
                            leanh::lean_dec(v___x_2391_);
                            v___x_2430_ = leanh::lean_box(0);
                            v_isShared_2431_ = v_isSharedCheck_2435_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2384_);
                    leanh::lean_dec_ref(v_lctx_2369_);
                    leanh::lean_dec_ref(v___f_2331_);
                    leanh::lean_dec(v_fvarId_2330_);
                    leanh::lean_dec(v___x_2329_);
                    leanh::lean_dec(v_mvarId_2328_);
                    v_a_2436_ = leanh::lean_ctor_get(v___x_2388_, 0);
                    v_isSharedCheck_2443_ = (!leanh::lean_is_exclusive(v___x_2388_)) as u8;
                    if v_isSharedCheck_2443_ == 0 {
                        v___x_2438_ = v___x_2388_;
                        v_isShared_2439_ = v_isSharedCheck_2443_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2436_);
                        leanh::lean_dec(v___x_2388_);
                        v___x_2438_ = leanh::lean_box(0);
                        v_isShared_2439_ = v_isSharedCheck_2443_;
                        state = 16;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2400_ = (leanh::lean_unbox(v_a_2396_) as u8);
                leanh::lean_dec(v_a_2396_);
                if v___x_2400_ == 0 {
                    leanh::lean_del_object(v___x_2398_);
                    leanh::lean_dec(v___x_2329_);
                    v___y_2371_ = v___x_2390_;
                    v___y_2372_ = v_a_2389_;
                    v___y_2373_ = v_type_2394_;
                    v___y_2374_ = v___y_2384_;
                    v___y_2375_ = v___y_2385_;
                    v___y_2376_ = v___y_2386_;
                    v___y_2377_ = v___y_2387_;
                    state = 6;
                    continue;
                } else {
                    v___x_2401_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_clear___lam__1___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_clear___lam__1___closed__1_once),
                        _init_l_Lean_MVarId_clear___lam__1___closed__1,
                    );
                    leanh::lean_inc(v_fvarId_2330_);
                    v___x_2402_ = l_Lean_mkFVar(v_fvarId_2330_);
                    v___x_2403_ = l_Lean_MessageData_ofExpr(v___x_2402_);
                    v___x_2404_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2404_, 0, v___x_2401_);
                    leanh::lean_ctor_set(v___x_2404_, 1, v___x_2403_);
                    v___x_2405_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
                    v___x_2406_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2406_, 0, v___x_2404_);
                    leanh::lean_ctor_set(v___x_2406_, 1, v___x_2405_);
                    if v_isShared_2399_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2398_, 1);
                        leanh::lean_ctor_set(v___x_2398_, 0, v___x_2406_);
                        v___x_2408_ = v___x_2398_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2406_);
                        v___x_2408_ = v_reuseFailAlloc_2418_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                leanh::lean_inc(v_mvarId_2328_);
                v___x_2409_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_2329_,
                    v_mvarId_2328_,
                    v___x_2408_,
                    v___y_2384_,
                    v___y_2385_,
                    v___y_2386_,
                    v___y_2387_,
                );
                if leanh::lean_obj_tag(v___x_2409_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2409_, 1);
                    v___y_2371_ = v___x_2390_;
                    v___y_2372_ = v_a_2389_;
                    v___y_2373_ = v_type_2394_;
                    v___y_2374_ = v___y_2384_;
                    v___y_2375_ = v___y_2385_;
                    v___y_2376_ = v___y_2386_;
                    v___y_2377_ = v___y_2387_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_type_2394_);
                    leanh::lean_dec(v_a_2389_);
                    leanh::lean_dec_ref(v___y_2384_);
                    leanh::lean_dec_ref(v_lctx_2369_);
                    leanh::lean_dec_ref(v___f_2331_);
                    leanh::lean_dec(v_fvarId_2330_);
                    leanh::lean_dec(v_mvarId_2328_);
                    v_a_2410_ = leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2417_ = (!leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2412_ = v___x_2409_;
                        v_isShared_2413_ = v_isSharedCheck_2417_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2410_);
                        leanh::lean_dec(v___x_2409_);
                        v___x_2412_ = leanh::lean_box(0);
                        v_isShared_2413_ = v_isSharedCheck_2417_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2413_ == 0 {
                    v___x_2415_ = v___x_2412_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
                    v___x_2415_ = v_reuseFailAlloc_2416_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2415_;
            }
            12 => {
                if v_isShared_2423_ == 0 {
                    v___x_2425_ = v___x_2422_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2425_;
            }
            14 => {
                if v_isShared_2431_ == 0 {
                    v___x_2433_ = v___x_2430_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
                    v___x_2433_ = v_reuseFailAlloc_2434_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2433_;
            }
            16 => {
                if v_isShared_2439_ == 0 {
                    v___x_2441_ = v___x_2438_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2442_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
                    v___x_2441_ = v_reuseFailAlloc_2442_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2441_;
            }
            18 => {
                if v_isShared_2456_ == 0 {
                    v___x_2458_ = v___x_2455_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
                    v___x_2458_ = v_reuseFailAlloc_2459_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2458_;
            }
            20 => {
                if v_isShared_2464_ == 0 {
                    v___x_2466_ = v___x_2463_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
                    v___x_2466_ = v_reuseFailAlloc_2467_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_clear___lam__1___boxed(
    mut v_mvarId_2469_: *mut leanh::LeanObject,
    mut v___x_2470_: *mut leanh::LeanObject,
    mut v_fvarId_2471_: *mut leanh::LeanObject,
    mut v___f_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ = l_Lean_MVarId_clear___lam__1(
        v_mvarId_2469_,
        v___x_2470_,
        v_fvarId_2471_,
        v___f_2472_,
        v___y_2473_,
        v___y_2474_,
        v___y_2475_,
        v___y_2476_,
    );
    leanh::lean_dec(v___y_2476_);
    leanh::lean_dec_ref(v___y_2475_);
    leanh::lean_dec(v___y_2474_);
    return v_res_2478_;
}
pub unsafe fn l_Lean_MVarId_clear(
    mut v_mvarId_2479_: *mut leanh::LeanObject,
    mut v_fvarId_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
    mut v_a_2482_: *mut leanh::LeanObject,
    mut v_a_2483_: *mut leanh::LeanObject,
    mut v_a_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_fvarId_2480_);
    v___f_2486_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_clear___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2486_, 0, v_fvarId_2480_);
    v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1;
    leanh::lean_inc(v_mvarId_2479_);
    v___f_2488_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_clear___lam__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_2488_, 0, v_mvarId_2479_);
    leanh::lean_closure_set(v___f_2488_, 1, v___x_2487_);
    leanh::lean_closure_set(v___f_2488_, 2, v_fvarId_2480_);
    leanh::lean_closure_set(v___f_2488_, 3, v___f_2486_);
    v___x_2489_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(
        v_mvarId_2479_,
        v___f_2488_,
        v_a_2481_,
        v_a_2482_,
        v_a_2483_,
        v_a_2484_,
    );
    return v___x_2489_;
}
pub unsafe fn l_Lean_MVarId_clear___boxed(
    mut v_mvarId_2490_: *mut leanh::LeanObject,
    mut v_fvarId_2491_: *mut leanh::LeanObject,
    mut v_a_2492_: *mut leanh::LeanObject,
    mut v_a_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
    mut v_a_2495_: *mut leanh::LeanObject,
    mut v_a_2496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lean_MVarId_clear(
        v_mvarId_2490_,
        v_fvarId_2491_,
        v_a_2492_,
        v_a_2493_,
        v_a_2494_,
        v_a_2495_,
    );
    leanh::lean_dec(v_a_2495_);
    leanh::lean_dec_ref(v_a_2494_);
    leanh::lean_dec(v_a_2493_);
    leanh::lean_dec_ref(v_a_2492_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(
    mut v_mvarId_2498_: *mut leanh::LeanObject,
    mut v_val_2499_: *mut leanh::LeanObject,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(
        v_mvarId_2498_,
        v_val_2499_,
        v___y_2501_,
    );
    return v___x_2505_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(
    mut v_mvarId_2506_: *mut leanh::LeanObject,
    mut v_val_2507_: *mut leanh::LeanObject,
    mut v___y_2508_: *mut leanh::LeanObject,
    mut v___y_2509_: *mut leanh::LeanObject,
    mut v___y_2510_: *mut leanh::LeanObject,
    mut v___y_2511_: *mut leanh::LeanObject,
    mut v___y_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(
        v_mvarId_2506_,
        v_val_2507_,
        v___y_2508_,
        v___y_2509_,
        v___y_2510_,
        v___y_2511_,
    );
    leanh::lean_dec(v___y_2511_);
    leanh::lean_dec_ref(v___y_2510_);
    leanh::lean_dec(v___y_2509_);
    leanh::lean_dec_ref(v___y_2508_);
    return v_res_2513_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(
    mut v_00_u03b2_2514_: *mut leanh::LeanObject,
    mut v_x_2515_: *mut leanh::LeanObject,
    mut v_x_2516_: *mut leanh::LeanObject,
    mut v_x_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_2515_, v_x_2516_, v_x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(
    mut v_00_u03b2_2519_: *mut leanh::LeanObject,
    mut v_x_2520_: *mut leanh::LeanObject,
    mut v_x_2521_: usize,
    mut v_x_2522_: usize,
    mut v_x_2523_: *mut leanh::LeanObject,
    mut v_x_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_2520_, v_x_2521_, v_x_2522_, v_x_2523_, v_x_2524_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(
    mut v_00_u03b2_2526_: *mut leanh::LeanObject,
    mut v_x_2527_: *mut leanh::LeanObject,
    mut v_x_2528_: *mut leanh::LeanObject,
    mut v_x_2529_: *mut leanh::LeanObject,
    mut v_x_2530_: *mut leanh::LeanObject,
    mut v_x_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10138__boxed_2532_: usize = 0;
    let mut v_x_10139__boxed_2533_: usize = 0;
    let mut v_res_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10138__boxed_2532_ = leanh::lean_unbox_usize(v_x_2528_);
    leanh::lean_dec(v_x_2528_);
    v_x_10139__boxed_2533_ = leanh::lean_unbox_usize(v_x_2529_);
    leanh::lean_dec(v_x_2529_);
    v_res_2534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_2526_, v_x_2527_, v_x_10138__boxed_2532_, v_x_10139__boxed_2533_, v_x_2530_, v_x_2531_);
    return v_res_2534_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(
    mut v_00_u03b2_2535_: *mut leanh::LeanObject,
    mut v_n_2536_: *mut leanh::LeanObject,
    mut v_k_2537_: *mut leanh::LeanObject,
    mut v_v_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_2536_, v_k_2537_, v_v_2538_);
    return v___x_2539_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(
    mut v_00_u03b2_2540_: *mut leanh::LeanObject,
    mut v_depth_2541_: usize,
    mut v_keys_2542_: *mut leanh::LeanObject,
    mut v_vals_2543_: *mut leanh::LeanObject,
    mut v_heq_2544_: *mut leanh::LeanObject,
    mut v_i_2545_: *mut leanh::LeanObject,
    mut v_entries_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_2541_, v_keys_2542_, v_vals_2543_, v_i_2545_, v_entries_2546_);
    return v___x_2547_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(
    mut v_00_u03b2_2548_: *mut leanh::LeanObject,
    mut v_depth_2549_: *mut leanh::LeanObject,
    mut v_keys_2550_: *mut leanh::LeanObject,
    mut v_vals_2551_: *mut leanh::LeanObject,
    mut v_heq_2552_: *mut leanh::LeanObject,
    mut v_i_2553_: *mut leanh::LeanObject,
    mut v_entries_2554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2555_: usize = 0;
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2555_ = leanh::lean_unbox_usize(v_depth_2549_);
    leanh::lean_dec(v_depth_2549_);
    v_res_2556_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_2548_, v_depth_boxed_2555_, v_keys_2550_, v_vals_2551_, v_heq_2552_, v_i_2553_, v_entries_2554_);
    leanh::lean_dec_ref(v_vals_2551_);
    leanh::lean_dec_ref(v_keys_2550_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(
    mut v_00_u03b2_2557_: *mut leanh::LeanObject,
    mut v_x_2558_: *mut leanh::LeanObject,
    mut v_x_2559_: *mut leanh::LeanObject,
    mut v_x_2560_: *mut leanh::LeanObject,
    mut v_x_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_2558_, v_x_2559_, v_x_2560_, v_x_2561_);
    return v___x_2562_;
}
pub unsafe fn l_Lean_MVarId_tryClear(
    mut v_mvarId_2563_: *mut leanh::LeanObject,
    mut v_fvarId_2564_: *mut leanh::LeanObject,
    mut v_a_2565_: *mut leanh::LeanObject,
    mut v_a_2566_: *mut leanh::LeanObject,
    mut v_a_2567_: *mut leanh::LeanObject,
    mut v_a_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2575_: u8 = 0;
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut v_unused_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: u8 = 0;
    let mut v_a_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2570_ = l_Lean_Meta_saveState___redArg(v_a_2566_, v_a_2568_);
                if leanh::lean_obj_tag(v___x_2570_) == 0 {
                    v_a_2571_ = leanh::lean_ctor_get(v___x_2570_, 0);
                    leanh::lean_inc(v_a_2571_);
                    leanh::lean_dec_ref_known(v___x_2570_, 1);
                    leanh::lean_inc(v_mvarId_2563_);
                    v___x_2572_ = l_Lean_MVarId_clear(
                        v_mvarId_2563_,
                        v_fvarId_2564_,
                        v_a_2565_,
                        v_a_2566_,
                        v_a_2567_,
                        v_a_2568_,
                    );
                    if leanh::lean_obj_tag(v___x_2572_) == 0 {
                        leanh::lean_dec(v_a_2571_);
                        leanh::lean_dec(v_mvarId_2563_);
                        return v___x_2572_;
                    } else {
                        v_a_2573_ = leanh::lean_ctor_get(v___x_2572_, 0);
                        leanh::lean_inc(v_a_2573_);
                        v___x_2593_ = l_Lean_Exception_isInterrupt(v_a_2573_);
                        if v___x_2593_ == 0 {
                            v___x_2594_ = l_Lean_Exception_isRuntime(v_a_2573_);
                            v___y_2575_ = v___x_2594_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2573_);
                            v___y_2575_ = v___x_2593_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_2564_);
                    leanh::lean_dec(v_mvarId_2563_);
                    v_a_2595_ = leanh::lean_ctor_get(v___x_2570_, 0);
                    v_isSharedCheck_2602_ = (!leanh::lean_is_exclusive(v___x_2570_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2597_ = v___x_2570_;
                        v_isShared_2598_ = v_isSharedCheck_2602_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2595_);
                        leanh::lean_dec(v___x_2570_);
                        v___x_2597_ = leanh::lean_box(0);
                        v_isShared_2598_ = v_isSharedCheck_2602_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2575_ == 0 {
                    leanh::lean_dec_ref_known(v___x_2572_, 1);
                    v___x_2576_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_2571_, v_a_2566_, v_a_2568_);
                    leanh::lean_dec(v_a_2571_);
                    if leanh::lean_obj_tag(v___x_2576_) == 0 {
                        v_isSharedCheck_2583_ =
                            (!leanh::lean_is_exclusive(v___x_2576_)) as u8;
                        if v_isSharedCheck_2583_ == 0 {
                            v_unused_2584_ = leanh::lean_ctor_get(v___x_2576_, 0);
                            leanh::lean_dec(v_unused_2584_);
                            v___x_2578_ = v___x_2576_;
                            v_isShared_2579_ = v_isSharedCheck_2583_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2576_);
                            v___x_2578_ = leanh::lean_box(0);
                            v_isShared_2579_ = v_isSharedCheck_2583_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_2563_);
                        v_a_2585_ = leanh::lean_ctor_get(v___x_2576_, 0);
                        v_isSharedCheck_2592_ =
                            (!leanh::lean_is_exclusive(v___x_2576_)) as u8;
                        if v_isSharedCheck_2592_ == 0 {
                            v___x_2587_ = v___x_2576_;
                            v_isShared_2588_ = v_isSharedCheck_2592_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2585_);
                            leanh::lean_dec(v___x_2576_);
                            v___x_2587_ = leanh::lean_box(0);
                            v_isShared_2588_ = v_isSharedCheck_2592_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2571_);
                    leanh::lean_dec(v_mvarId_2563_);
                    return v___x_2572_;
                }
            }
            2 => {
                if v_isShared_2579_ == 0 {
                    leanh::lean_ctor_set(v___x_2578_, 0, v_mvarId_2563_);
                    v___x_2581_ = v___x_2578_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2582_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_mvarId_2563_);
                    v___x_2581_ = v_reuseFailAlloc_2582_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2581_;
            }
            4 => {
                if v_isShared_2588_ == 0 {
                    v___x_2590_ = v___x_2587_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
                    v___x_2590_ = v_reuseFailAlloc_2591_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2590_;
            }
            6 => {
                if v_isShared_2598_ == 0 {
                    v___x_2600_ = v___x_2597_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
                    v___x_2600_ = v_reuseFailAlloc_2601_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_tryClear___boxed(
    mut v_mvarId_2603_: *mut leanh::LeanObject,
    mut v_fvarId_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
    mut v_a_2607_: *mut leanh::LeanObject,
    mut v_a_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2610_ = l_Lean_MVarId_tryClear(
        v_mvarId_2603_,
        v_fvarId_2604_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
        v_a_2608_,
    );
    leanh::lean_dec(v_a_2608_);
    leanh::lean_dec_ref(v_a_2607_);
    leanh::lean_dec(v_a_2606_);
    leanh::lean_dec_ref(v_a_2605_);
    return v_res_2610_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(
    mut v_as_2611_: *mut leanh::LeanObject,
    mut v_i_2612_: usize,
    mut v_stop_2613_: usize,
    mut v_b_2614_: *mut leanh::LeanObject,
    mut v___y_2615_: *mut leanh::LeanObject,
    mut v___y_2616_: *mut leanh::LeanObject,
    mut v___y_2617_: *mut leanh::LeanObject,
    mut v___y_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2620_: u8 = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: usize = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2620_ = lean_usize_dec_eq(v_i_2612_, v_stop_2613_);
                if v___x_2620_ == 0 {
                    v___x_2621_ = 1usize;
                    v___x_2622_ = lean_usize_sub(v_i_2612_, v___x_2621_);
                    v___x_2623_ = lean_array_uget_borrowed(v_as_2611_, v___x_2622_);
                    leanh::lean_inc(v___x_2623_);
                    v___x_2624_ = l_Lean_MVarId_tryClear(
                        v_b_2614_,
                        v___x_2623_,
                        v___y_2615_,
                        v___y_2616_,
                        v___y_2617_,
                        v___y_2618_,
                    );
                    if leanh::lean_obj_tag(v___x_2624_) == 0 {
                        v_a_2625_ = leanh::lean_ctor_get(v___x_2624_, 0);
                        leanh::lean_inc(v_a_2625_);
                        leanh::lean_dec_ref_known(v___x_2624_, 1);
                        v_i_2612_ = v___x_2622_;
                        v_b_2614_ = v_a_2625_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2624_;
                    }
                } else {
                    v___x_2627_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2627_, 0, v_b_2614_);
                    return v___x_2627_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(
    mut v_as_2628_: *mut leanh::LeanObject,
    mut v_i_2629_: *mut leanh::LeanObject,
    mut v_stop_2630_: *mut leanh::LeanObject,
    mut v_b_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
    mut v___y_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2637_: usize = 0;
    let mut v_stop_boxed_2638_: usize = 0;
    let mut v_res_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2637_ = leanh::lean_unbox_usize(v_i_2629_);
    leanh::lean_dec(v_i_2629_);
    v_stop_boxed_2638_ = leanh::lean_unbox_usize(v_stop_2630_);
    leanh::lean_dec(v_stop_2630_);
    v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_2628_, v_i_boxed_2637_, v_stop_boxed_2638_, v_b_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
    leanh::lean_dec(v___y_2635_);
    leanh::lean_dec_ref(v___y_2634_);
    leanh::lean_dec(v___y_2633_);
    leanh::lean_dec_ref(v___y_2632_);
    leanh::lean_dec_ref(v_as_2628_);
    return v_res_2639_;
}
pub unsafe fn l_Lean_MVarId_tryClearMany(
    mut v_mvarId_2640_: *mut leanh::LeanObject,
    mut v_fvarIds_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    v___x_2647_ = lean_array_get_size(v_fvarIds_2641_);
    v___x_2648_ = leanh::lean_unsigned_to_nat(0);
    v___x_2649_ = lean_nat_dec_lt(v___x_2648_, v___x_2647_);
    if v___x_2649_ == 0 {
        let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2650_, 0, v_mvarId_2640_);
        return v___x_2650_;
    } else {
        let mut v___x_2651_: usize = 0;
        let mut v___x_2652_: usize = 0;
        let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2651_ = lean_usize_of_nat(v___x_2647_);
        v___x_2652_ = 0usize;
        v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_2641_, v___x_2651_, v___x_2652_, v_mvarId_2640_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
        return v___x_2653_;
    }
}
pub unsafe fn l_Lean_MVarId_tryClearMany___boxed(
    mut v_mvarId_2654_: *mut leanh::LeanObject,
    mut v_fvarIds_2655_: *mut leanh::LeanObject,
    mut v_a_2656_: *mut leanh::LeanObject,
    mut v_a_2657_: *mut leanh::LeanObject,
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
    mut v_a_2660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2661_ = l_Lean_MVarId_tryClearMany(
        v_mvarId_2654_,
        v_fvarIds_2655_,
        v_a_2656_,
        v_a_2657_,
        v_a_2658_,
        v_a_2659_,
    );
    leanh::lean_dec(v_a_2659_);
    leanh::lean_dec_ref(v_a_2658_);
    leanh::lean_dec(v_a_2657_);
    leanh::lean_dec_ref(v_a_2656_);
    leanh::lean_dec_ref(v_fvarIds_2655_);
    return v_res_2661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(
    mut v_as_2662_: *mut leanh::LeanObject,
    mut v_i_2663_: usize,
    mut v_stop_2664_: usize,
    mut v_b_2665_: *mut leanh::LeanObject,
    mut v___y_2666_: *mut leanh::LeanObject,
    mut v___y_2667_: *mut leanh::LeanObject,
    mut v___y_2668_: *mut leanh::LeanObject,
    mut v___y_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2671_: u8 = 0;
    let mut v_fst_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2677_: usize = 0;
    let mut v___x_2678_: usize = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_isSharedCheck_2698_: u8 = 0;
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2671_ = lean_usize_dec_eq(v_i_2663_, v_stop_2664_);
                if v___x_2671_ == 0 {
                    v_fst_2672_ = leanh::lean_ctor_get(v_b_2665_, 0);
                    v_snd_2673_ = leanh::lean_ctor_get(v_b_2665_, 1);
                    v_isSharedCheck_2698_ = (!leanh::lean_is_exclusive(v_b_2665_)) as u8;
                    if v_isSharedCheck_2698_ == 0 {
                        v___x_2675_ = v_b_2665_;
                        v_isShared_2676_ = v_isSharedCheck_2698_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2673_);
                        leanh::lean_inc(v_fst_2672_);
                        leanh::lean_dec(v_b_2665_);
                        v___x_2675_ = leanh::lean_box(0);
                        v_isShared_2676_ = v_isSharedCheck_2698_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2699_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2699_, 0, v_b_2665_);
                    return v___x_2699_;
                }
            }
            1 => {
                v___x_2677_ = 1usize;
                v___x_2678_ = lean_usize_sub(v_i_2663_, v___x_2677_);
                v___x_2679_ = lean_array_uget_borrowed(v_as_2662_, v___x_2678_);
                leanh::lean_inc(v___x_2679_);
                leanh::lean_inc(v_fst_2672_);
                v___x_2680_ = l_Lean_MVarId_tryClear(
                    v_fst_2672_,
                    v___x_2679_,
                    v___y_2666_,
                    v___y_2667_,
                    v___y_2668_,
                    v___y_2669_,
                );
                if leanh::lean_obj_tag(v___x_2680_) == 0 {
                    v_a_2681_ = leanh::lean_ctor_get(v___x_2680_, 0);
                    leanh::lean_inc(v_a_2681_);
                    leanh::lean_dec_ref_known(v___x_2680_, 1);
                    v___x_2688_ = l_Lean_instBEqMVarId_beq(v_fst_2672_, v_a_2681_);
                    leanh::lean_dec(v_fst_2672_);
                    if v___x_2688_ == 0 {
                        leanh::lean_inc(v___x_2679_);
                        v___x_2689_ = lean_array_push(v_snd_2673_, v___x_2679_);
                        v___y_2683_ = v___x_2689_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2683_ = v_snd_2673_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2675_);
                    leanh::lean_dec(v_snd_2673_);
                    leanh::lean_dec(v_fst_2672_);
                    v_a_2690_ = leanh::lean_ctor_get(v___x_2680_, 0);
                    v_isSharedCheck_2697_ = (!leanh::lean_is_exclusive(v___x_2680_)) as u8;
                    if v_isSharedCheck_2697_ == 0 {
                        v___x_2692_ = v___x_2680_;
                        v_isShared_2693_ = v_isSharedCheck_2697_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2690_);
                        leanh::lean_dec(v___x_2680_);
                        v___x_2692_ = leanh::lean_box(0);
                        v_isShared_2693_ = v_isSharedCheck_2697_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2676_ == 0 {
                    leanh::lean_ctor_set(v___x_2675_, 1, v___y_2683_);
                    leanh::lean_ctor_set(v___x_2675_, 0, v_a_2681_);
                    v___x_2685_ = v___x_2675_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___y_2683_);
                    v___x_2685_ = v_reuseFailAlloc_2687_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_i_2663_ = v___x_2678_;
                v_b_2665_ = v___x_2685_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2693_ == 0 {
                    v___x_2695_ = v___x_2692_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
                    v___x_2695_ = v_reuseFailAlloc_2696_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(
    mut v_as_2700_: *mut leanh::LeanObject,
    mut v_i_2701_: *mut leanh::LeanObject,
    mut v_stop_2702_: *mut leanh::LeanObject,
    mut v_b_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
    mut v___y_2708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2709_: usize = 0;
    let mut v_stop_boxed_2710_: usize = 0;
    let mut v_res_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2709_ = leanh::lean_unbox_usize(v_i_2701_);
    leanh::lean_dec(v_i_2701_);
    v_stop_boxed_2710_ = leanh::lean_unbox_usize(v_stop_2702_);
    leanh::lean_dec(v_stop_2702_);
    v_res_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_2700_, v_i_boxed_2709_, v_stop_boxed_2710_, v_b_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
    leanh::lean_dec(v___y_2707_);
    leanh::lean_dec_ref(v___y_2706_);
    leanh::lean_dec(v___y_2705_);
    leanh::lean_dec_ref(v___y_2704_);
    leanh::lean_dec_ref(v_as_2700_);
    return v_res_2711_;
}
pub unsafe fn l_Lean_MVarId_tryClearMany_x27___lam__0(
    mut v_fvarIds_2712_: *mut leanh::LeanObject,
    mut v_goal_2713_: *mut leanh::LeanObject,
    mut v___y_2714_: *mut leanh::LeanObject,
    mut v___y_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: u8 = 0;
    v_lctx_2719_ = leanh::lean_ctor_get(v___y_2714_, 2);
    v___x_2720_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_2719_, v_fvarIds_2712_);
    v___x_2721_ = lean_array_get_size(v___x_2720_);
    v___x_2722_ = lean_mk_empty_array_with_capacity(v___x_2721_);
    v___x_2723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2723_, 0, v_goal_2713_);
    leanh::lean_ctor_set(v___x_2723_, 1, v___x_2722_);
    v___x_2724_ = leanh::lean_unsigned_to_nat(0);
    v___x_2725_ = lean_nat_dec_lt(v___x_2724_, v___x_2721_);
    if v___x_2725_ == 0 {
        let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2720_);
        v___x_2726_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2726_, 0, v___x_2723_);
        return v___x_2726_;
    } else {
        let mut v___x_2727_: usize = 0;
        let mut v___x_2728_: usize = 0;
        let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2727_ = lean_usize_of_nat(v___x_2721_);
        v___x_2728_ = 0usize;
        v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_2720_, v___x_2727_, v___x_2728_, v___x_2723_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
        leanh::lean_dec_ref(v___x_2720_);
        return v___x_2729_;
    }
}
pub unsafe fn l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(
    mut v_fvarIds_2730_: *mut leanh::LeanObject,
    mut v_goal_2731_: *mut leanh::LeanObject,
    mut v___y_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
    mut v___y_2734_: *mut leanh::LeanObject,
    mut v___y_2735_: *mut leanh::LeanObject,
    mut v___y_2736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2737_ = l_Lean_MVarId_tryClearMany_x27___lam__0(
        v_fvarIds_2730_,
        v_goal_2731_,
        v___y_2732_,
        v___y_2733_,
        v___y_2734_,
        v___y_2735_,
    );
    leanh::lean_dec(v___y_2735_);
    leanh::lean_dec_ref(v___y_2734_);
    leanh::lean_dec(v___y_2733_);
    leanh::lean_dec_ref(v___y_2732_);
    return v_res_2737_;
}
pub unsafe fn l_Lean_MVarId_tryClearMany_x27(
    mut v_goal_2738_: *mut leanh::LeanObject,
    mut v_fvarIds_2739_: *mut leanh::LeanObject,
    mut v_a_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_goal_2738_);
    v___f_2745_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_tryClearMany_x27___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_2745_, 0, v_fvarIds_2739_);
    leanh::lean_closure_set(v___f_2745_, 1, v_goal_2738_);
    v___x_2746_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(
        v_goal_2738_,
        v___f_2745_,
        v_a_2740_,
        v_a_2741_,
        v_a_2742_,
        v_a_2743_,
    );
    return v___x_2746_;
}
pub unsafe fn l_Lean_MVarId_tryClearMany_x27___boxed(
    mut v_goal_2747_: *mut leanh::LeanObject,
    mut v_fvarIds_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
    mut v_a_2751_: *mut leanh::LeanObject,
    mut v_a_2752_: *mut leanh::LeanObject,
    mut v_a_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2754_ = l_Lean_MVarId_tryClearMany_x27(
        v_goal_2747_,
        v_fvarIds_2748_,
        v_a_2749_,
        v_a_2750_,
        v_a_2751_,
        v_a_2752_,
    );
    leanh::lean_dec(v_a_2752_);
    leanh::lean_dec_ref(v_a_2751_);
    leanh::lean_dec(v_a_2750_);
    leanh::lean_dec_ref(v_a_2749_);
    return v_res_2754_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Clear(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Clear(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Clear(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Clear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Clear(builtin);
}