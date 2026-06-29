// Lean compiler output
// Module: Lean.Meta.Sym.Simp.CongrInfo
// Imports: Lean.Meta.Sym.SymM Lean.Meta.FunInfo Init.Omega
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::CongrTheorems::{
    l_Lean_Meta_getCongrSimpKinds, l_Lean_Meta_instBEqCongrArgKind_beq,
    l_Lean_Meta_mkCongrSimpCore_x3f, l_Lean_Meta_mkCongrSimpForConst_x3f,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_getFunInfo, runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [102, 105, 120, 101, 100, 80, 114, 101, 102, 105, 120, 32, 0]};
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 108, 97, 99, 101, 100, 32, 0]};
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 111, 110, 103, 114, 84, 104, 101, 111, 114, 101, 109, 32, 0]};
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(
    mut v_argKinds_796_: *mut crate::leanh::LeanObject,
    mut v_pre_797_: *mut crate::leanh::LeanObject,
    mut v_i_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: u8 = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_799_ = lean_array_get_size(v_argKinds_796_);
                v___x_800_ = lean_nat_dec_lt(v_i_798_, v___x_799_);
                if v___x_800_ == 0 {
                    crate::leanh::lean_dec(v_i_798_);
                    v___x_801_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_801_, 0, v_pre_797_);
                    return v___x_801_;
                } else {
                    v___x_802_ = lean_array_fget_borrowed(v_argKinds_796_, v_i_798_);
                    v___x_803_ = (crate::leanh::lean_unbox(v___x_802_) as u8);
                    match v___x_803_ {
                        0 => {
                            crate::leanh::lean_dec(v_i_798_);
                            crate::leanh::lean_dec(v_pre_797_);
                            v___x_804_ = crate::leanh::lean_box(0);
                            return v___x_804_;
                        }
                        2 => {
                            v___x_805_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_806_ = lean_nat_add(v_i_798_, v___x_805_);
                            crate::leanh::lean_dec(v_i_798_);
                            v_i_798_ = v___x_806_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_i_798_);
                            crate::leanh::lean_dec(v_pre_797_);
                            v___x_808_ = crate::leanh::lean_box(0);
                            return v___x_808_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq___boxed(
    mut v_argKinds_809_: *mut crate::leanh::LeanObject,
    mut v_pre_810_: *mut crate::leanh::LeanObject,
    mut v_i_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(
        v_argKinds_809_,
        v_pre_810_,
        v_i_811_,
    );
    crate::leanh::lean_dec_ref(v_argKinds_809_);
    return v_res_812_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(
    mut v_x_813_: u8,
    mut v_h__1_814_: *mut crate::leanh::LeanObject,
    mut v_h__2_815_: *mut crate::leanh::LeanObject,
    mut v_h__3_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_813_ {
        0 => {
            let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_816_);
            crate::leanh::lean_dec(v_h__2_815_);
            v___x_817_ = crate::leanh::lean_box(0);
            v___x_818_ = crate::leanh::lean_apply_1(v_h__1_814_, v___x_817_);
            return v___x_818_;
        }
        2 => {
            let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_816_);
            crate::leanh::lean_dec(v_h__1_814_);
            v___x_819_ = crate::leanh::lean_box(0);
            v___x_820_ = crate::leanh::lean_apply_1(v_h__2_815_, v___x_819_);
            return v___x_820_;
        }
        _ => {
            let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_815_);
            crate::leanh::lean_dec(v_h__1_814_);
            v___x_821_ = crate::leanh::lean_box((v_x_813_) as usize);
            v___x_822_ = crate::leanh::lean_apply_3(
                v_h__3_816_,
                v___x_821_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_822_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg___boxed(
    mut v_x_823_: *mut crate::leanh::LeanObject,
    mut v_h__1_824_: *mut crate::leanh::LeanObject,
    mut v_h__2_825_: *mut crate::leanh::LeanObject,
    mut v_h__3_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_22__boxed_827_: u8 = 0;
    let mut v_res_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_22__boxed_827_ = (crate::leanh::lean_unbox(v_x_823_) as u8);
    v_res_828_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(v_x_22__boxed_827_, v_h__1_824_, v_h__2_825_, v_h__3_826_);
    return v_res_828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(
    mut v_motive_829_: *mut crate::leanh::LeanObject,
    mut v_x_830_: u8,
    mut v_h__1_831_: *mut crate::leanh::LeanObject,
    mut v_h__2_832_: *mut crate::leanh::LeanObject,
    mut v_h__3_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_830_ {
        0 => {
            let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_833_);
            crate::leanh::lean_dec(v_h__2_832_);
            v___x_834_ = crate::leanh::lean_box(0);
            v___x_835_ = crate::leanh::lean_apply_1(v_h__1_831_, v___x_834_);
            return v___x_835_;
        }
        2 => {
            let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_833_);
            crate::leanh::lean_dec(v_h__1_831_);
            v___x_836_ = crate::leanh::lean_box(0);
            v___x_837_ = crate::leanh::lean_apply_1(v_h__2_832_, v___x_836_);
            return v___x_837_;
        }
        _ => {
            let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_832_);
            crate::leanh::lean_dec(v_h__1_831_);
            v___x_838_ = crate::leanh::lean_box((v_x_830_) as usize);
            v___x_839_ = crate::leanh::lean_apply_3(
                v_h__3_833_,
                v___x_838_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_839_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___boxed(
    mut v_motive_840_: *mut crate::leanh::LeanObject,
    mut v_x_841_: *mut crate::leanh::LeanObject,
    mut v_h__1_842_: *mut crate::leanh::LeanObject,
    mut v_h__2_843_: *mut crate::leanh::LeanObject,
    mut v_h__3_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_845_: u8 = 0;
    let mut v_res_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_845_ = (crate::leanh::lean_unbox(v_x_841_) as u8);
    v_res_846_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(v_motive_840_, v_x_37__boxed_845_, v_h__1_842_, v_h__2_843_, v_h__3_844_);
    return v_res_846_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(
    mut v_argKinds_847_: *mut crate::leanh::LeanObject,
    mut v_i_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_849_ = lean_array_get_size(v_argKinds_847_);
                v___x_850_ = lean_nat_dec_lt(v_i_848_, v___x_849_);
                if v___x_850_ == 0 {
                    crate::leanh::lean_dec(v_i_848_);
                    v___x_851_ = crate::leanh::lean_box(0);
                    return v___x_851_;
                } else {
                    v___x_852_ = lean_array_fget_borrowed(v_argKinds_847_, v_i_848_);
                    v___x_853_ = (crate::leanh::lean_unbox(v___x_852_) as u8);
                    match v___x_853_ {
                        0 => {
                            v___x_854_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_855_ = lean_nat_add(v_i_848_, v___x_854_);
                            crate::leanh::lean_dec(v_i_848_);
                            v_i_848_ = v___x_855_;
                            state = 0;
                            continue;
                        }
                        2 => {
                            v___x_857_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_858_ = lean_nat_add(v_i_848_, v___x_857_);
                            v___x_859_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(v_argKinds_847_, v_i_848_, v___x_858_);
                            return v___x_859_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_i_848_);
                            v___x_860_ = crate::leanh::lean_box(0);
                            return v___x_860_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go___boxed(
    mut v_argKinds_861_: *mut crate::leanh::LeanObject,
    mut v_i_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_863_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(
        v_argKinds_861_,
        v_i_862_,
    );
    crate::leanh::lean_dec_ref(v_argKinds_861_);
    return v_res_863_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(
    mut v_argKinds_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_866_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(
        v_argKinds_864_,
        v___x_865_,
    );
    return v___x_866_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f___boxed(
    mut v_argKinds_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_868_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(
        v_argKinds_867_,
    );
    crate::leanh::lean_dec_ref(v_argKinds_867_);
    return v_res_868_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(
    mut v_xs_869_: *mut crate::leanh::LeanObject,
    mut v_ys_870_: *mut crate::leanh::LeanObject,
    mut v_x_871_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_873_: u8 = 0;
    let mut v_one_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_872_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_873_ = lean_nat_dec_eq(v_x_871_, v_zero_872_);
                if v_isZero_873_ == 1 {
                    crate::leanh::lean_dec(v_x_871_);
                    return v_isZero_873_;
                } else {
                    v_one_874_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_875_ = lean_nat_sub(v_x_871_, v_one_874_);
                    crate::leanh::lean_dec(v_x_871_);
                    v___x_876_ = lean_array_fget_borrowed(v_xs_869_, v_n_875_);
                    v___x_877_ = lean_array_fget_borrowed(v_ys_870_, v_n_875_);
                    v___x_878_ = (crate::leanh::lean_unbox(v___x_876_) as u8);
                    v___x_879_ = (crate::leanh::lean_unbox(v___x_877_) as u8);
                    v___x_880_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_878_, v___x_879_);
                    if v___x_880_ == 0 {
                        crate::leanh::lean_dec(v_n_875_);
                        return v___x_880_;
                    } else {
                        v_x_871_ = v_n_875_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg___boxed(
    mut v_xs_882_: *mut crate::leanh::LeanObject,
    mut v_ys_883_: *mut crate::leanh::LeanObject,
    mut v_x_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_885_: u8 = 0;
    let mut v_r_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_882_, v_ys_883_, v_x_884_);
    crate::leanh::lean_dec_ref(v_ys_883_);
    crate::leanh::lean_dec_ref(v_xs_882_);
    v_r_886_ = crate::leanh::lean_box((v_res_885_) as usize);
    return v_r_886_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(
    mut v___y_887_: u8,
    mut v_a_888_: u8,
    mut v_as_889_: *mut crate::leanh::LeanObject,
    mut v_i_890_: usize,
    mut v_stop_891_: usize,
) -> u8 {
    let mut v___x_892_: u8 = 0;
    let mut v___x_893_: u8 = 0;
    let mut v___y_895_: u8 = 0;
    let mut v___x_896_: usize = 0;
    let mut v___x_897_: usize = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_892_ = lean_usize_dec_eq(v_i_890_, v_stop_891_);
                if v___x_892_ == 0 {
                    v___x_893_ = 1;
                    v___x_899_ = lean_array_uget_borrowed(v_as_889_, v_i_890_);
                    v___x_900_ = 0;
                    v___x_901_ = (crate::leanh::lean_unbox(v___x_899_) as u8);
                    v___x_902_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_901_, v___x_900_);
                    if v___x_902_ == 0 {
                        v___y_895_ = v___y_887_;
                        state = 1;
                        continue;
                    } else {
                        v___y_895_ = v_a_888_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_903_ = 0;
                    return v___x_903_;
                }
            }
            1 => {
                if v___y_895_ == 0 {
                    v___x_896_ = 1usize;
                    v___x_897_ = lean_usize_add(v_i_890_, v___x_896_);
                    v_i_890_ = v___x_897_;
                    state = 0;
                    continue;
                } else {
                    return v___x_893_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v_a_905_: *mut crate::leanh::LeanObject,
    mut v_as_906_: *mut crate::leanh::LeanObject,
    mut v_i_907_: *mut crate::leanh::LeanObject,
    mut v_stop_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7889__boxed_909_: u8 = 0;
    let mut v_a_7890__boxed_910_: u8 = 0;
    let mut v_i_boxed_911_: usize = 0;
    let mut v_stop_boxed_912_: usize = 0;
    let mut v_res_913_: u8 = 0;
    let mut v_r_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_7889__boxed_909_ = (crate::leanh::lean_unbox(v___y_904_) as u8);
    v_a_7890__boxed_910_ = (crate::leanh::lean_unbox(v_a_905_) as u8);
    v_i_boxed_911_ = crate::leanh::lean_unbox_usize(v_i_907_);
    crate::leanh::lean_dec(v_i_907_);
    v_stop_boxed_912_ = crate::leanh::lean_unbox_usize(v_stop_908_);
    crate::leanh::lean_dec(v_stop_908_);
    v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_7889__boxed_909_, v_a_7890__boxed_910_, v_as_906_, v_i_boxed_911_, v_stop_boxed_912_);
    crate::leanh::lean_dec_ref(v_as_906_);
    v_r_914_ = crate::leanh::lean_box((v_res_913_) as usize);
    return v_r_914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(
    mut v_sz_915_: usize,
    mut v_i_916_: usize,
    mut v_bs_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_918_: u8 = 0;
    let mut v_v_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: u8 = 0;
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: usize = 0;
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_918_ = lean_usize_dec_lt(v_i_916_, v_sz_915_);
                if v___x_918_ == 0 {
                    return v_bs_917_;
                } else {
                    v_v_919_ = lean_array_uget(v_bs_917_, v_i_916_);
                    v___x_920_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_921_ = lean_array_uset(v_bs_917_, v_i_916_, v___x_920_);
                    v___x_922_ = 2;
                    v___x_923_ = (crate::leanh::lean_unbox(v_v_919_) as u8);
                    crate::leanh::lean_dec(v_v_919_);
                    v___x_924_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_923_, v___x_922_);
                    v___x_925_ = 1usize;
                    v___x_926_ = lean_usize_add(v_i_916_, v___x_925_);
                    v___x_927_ = crate::leanh::lean_box((v___x_924_) as usize);
                    v___x_928_ = lean_array_uset(v_bs_x27_921_, v_i_916_, v___x_927_);
                    v_i_916_ = v___x_926_;
                    v_bs_917_ = v___x_928_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(
    mut v_sz_930_: *mut crate::leanh::LeanObject,
    mut v_i_931_: *mut crate::leanh::LeanObject,
    mut v_bs_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_933_: usize = 0;
    let mut v_i_boxed_934_: usize = 0;
    let mut v_res_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_933_ = crate::leanh::lean_unbox_usize(v_sz_930_);
    crate::leanh::lean_dec(v_sz_930_);
    v_i_boxed_934_ = crate::leanh::lean_unbox_usize(v_i_931_);
    crate::leanh::lean_dec(v_i_931_);
    v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_boxed_933_, v_i_boxed_934_, v_bs_932_);
    return v_res_935_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(
    mut v_a_936_: u8,
    mut v_as_937_: *mut crate::leanh::LeanObject,
    mut v_i_938_: usize,
    mut v_stop_939_: usize,
) -> u8 {
    let mut v___x_940_: u8 = 0;
    let mut v___x_941_: u8 = 0;
    let mut v___y_943_: u8 = 0;
    let mut v___x_944_: usize = 0;
    let mut v___x_945_: usize = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v___x_949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_940_ = lean_usize_dec_eq(v_i_938_, v_stop_939_);
                if v___x_940_ == 0 {
                    v___x_941_ = 1;
                    v___x_947_ = lean_array_uget_borrowed(v_as_937_, v_i_938_);
                    v___x_948_ = (crate::leanh::lean_unbox(v___x_947_) as u8);
                    match v___x_948_ {
                        0 => {
                            v___y_943_ = v_a_936_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___y_943_ = v_a_936_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            return v___x_941_;
                        }
                    }
                } else {
                    v___x_949_ = 0;
                    return v___x_949_;
                }
            }
            1 => {
                if v___y_943_ == 0 {
                    v___x_944_ = 1usize;
                    v___x_945_ = lean_usize_add(v_i_938_, v___x_944_);
                    v_i_938_ = v___x_945_;
                    state = 0;
                    continue;
                } else {
                    return v___x_941_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_as_951_: *mut crate::leanh::LeanObject,
    mut v_i_952_: *mut crate::leanh::LeanObject,
    mut v_stop_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7939__boxed_954_: u8 = 0;
    let mut v_i_boxed_955_: usize = 0;
    let mut v_stop_boxed_956_: usize = 0;
    let mut v_res_957_: u8 = 0;
    let mut v_r_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_7939__boxed_954_ = (crate::leanh::lean_unbox(v_a_950_) as u8);
    v_i_boxed_955_ = crate::leanh::lean_unbox_usize(v_i_952_);
    crate::leanh::lean_dec(v_i_952_);
    v_stop_boxed_956_ = crate::leanh::lean_unbox_usize(v_stop_953_);
    crate::leanh::lean_dec(v_stop_953_);
    v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_7939__boxed_954_, v_as_951_, v_i_boxed_955_, v_stop_boxed_956_);
    crate::leanh::lean_dec_ref(v_as_951_);
    v_r_958_ = crate::leanh::lean_box((v_res_957_) as usize);
    return v_r_958_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(
    mut v_f_959_: *mut crate::leanh::LeanObject,
    mut v_a_960_: *mut crate::leanh::LeanObject,
    mut v_a_961_: *mut crate::leanh::LeanObject,
    mut v_a_962_: *mut crate::leanh::LeanObject,
    mut v_a_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_970_: u8 = 0;
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_981_: u8 = 0;
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_990_: u8 = 0;
    let mut v___x_991_: u8 = 0;
    let mut v___x_992_: usize = 0;
    let mut v___x_993_: usize = 0;
    let mut v___x_994_: u8 = 0;
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1003_: usize = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: u8 = 0;
    let mut v___y_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v_val_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1023_: u8 = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut v_a_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut v___x_1044_: u8 = 0;
    let mut v___x_1045_: usize = 0;
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: u8 = 0;
    let mut v___x_1048_: u8 = 0;
    let mut v_declName_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v_val_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v_argKinds_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: u8 = 0;
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut v_a_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_a_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v_a_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut v_a_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1106_: u8 = 0;
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_f_959_);
                v___x_965_ = l_Lean_Meta_isProof(v_f_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
                if crate::leanh::lean_obj_tag(v___x_965_) == 0 {
                    v_a_966_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
                    v_isSharedCheck_1102_ = (!crate::leanh::lean_is_exclusive(v___x_965_)) as u8;
                    if v_isSharedCheck_1102_ == 0 {
                        v___x_968_ = v___x_965_;
                        v_isShared_969_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_966_);
                        crate::leanh::lean_dec(v___x_965_);
                        v___x_968_ = crate::leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_959_);
                    v_a_1103_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
                    v_isSharedCheck_1110_ = (!crate::leanh::lean_is_exclusive(v___x_965_)) as u8;
                    if v_isSharedCheck_1110_ == 0 {
                        v___x_1105_ = v___x_965_;
                        v_isShared_1106_ = v_isSharedCheck_1110_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1103_);
                        crate::leanh::lean_dec(v___x_965_);
                        v___x_1105_ = crate::leanh::lean_box(0);
                        v_isShared_1106_ = v_isSharedCheck_1110_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                v___x_970_ = (crate::leanh::lean_unbox(v_a_966_) as u8);
                if v___x_970_ == 0 {
                    crate::leanh::lean_del_object(v___x_968_);
                    v___x_971_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_f_959_);
                    v___x_972_ = l_Lean_Meta_getFunInfo(
                        v_f_959_, v___x_971_, v_a_960_, v_a_961_, v_a_962_, v_a_963_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_972_) == 0 {
                        v_a_973_ = crate::leanh::lean_ctor_get(v___x_972_, 0);
                        v_isSharedCheck_1089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_972_)) as u8;
                        if v_isSharedCheck_1089_ == 0 {
                            v___x_975_ = v___x_972_;
                            v_isShared_976_ = v_isSharedCheck_1089_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_973_);
                            crate::leanh::lean_dec(v___x_972_);
                            v___x_975_ = crate::leanh::lean_box(0);
                            v_isShared_976_ = v_isSharedCheck_1089_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_966_);
                        crate::leanh::lean_dec_ref(v_f_959_);
                        v_a_1090_ = crate::leanh::lean_ctor_get(v___x_972_, 0);
                        v_isSharedCheck_1097_ =
                            (!crate::leanh::lean_is_exclusive(v___x_972_)) as u8;
                        if v_isSharedCheck_1097_ == 0 {
                            v___x_1092_ = v___x_972_;
                            v_isShared_1093_ = v_isSharedCheck_1097_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1090_);
                            crate::leanh::lean_dec(v___x_972_);
                            v___x_1092_ = crate::leanh::lean_box(0);
                            v_isShared_1093_ = v_isSharedCheck_1097_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_966_);
                    crate::leanh::lean_dec_ref(v_f_959_);
                    v___x_1098_ = crate::leanh::lean_box(0);
                    if v_isShared_969_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_1098_);
                        v___x_1100_ = v___x_968_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_1101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
                        v___x_1100_ = v_reuseFailAlloc_1101_;
                        state = 27;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_f_959_);
                v___x_977_ = l_Lean_Meta_getCongrSimpKinds(
                    v_f_959_, v_a_973_, v_a_960_, v_a_961_, v_a_962_, v_a_963_,
                );
                if crate::leanh::lean_obj_tag(v___x_977_) == 0 {
                    v_a_978_ = crate::leanh::lean_ctor_get(v___x_977_, 0);
                    v_isSharedCheck_1080_ = (!crate::leanh::lean_is_exclusive(v___x_977_)) as u8;
                    if v_isSharedCheck_1080_ == 0 {
                        v___x_980_ = v___x_977_;
                        v_isShared_981_ = v_isSharedCheck_1080_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_978_);
                        crate::leanh::lean_dec(v___x_977_);
                        v___x_980_ = crate::leanh::lean_box(0);
                        v_isShared_981_ = v_isSharedCheck_1080_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_975_);
                    crate::leanh::lean_dec(v_a_973_);
                    crate::leanh::lean_dec(v_a_966_);
                    crate::leanh::lean_dec_ref(v_f_959_);
                    v_a_1081_ = crate::leanh::lean_ctor_get(v___x_977_, 0);
                    v_isSharedCheck_1088_ = (!crate::leanh::lean_is_exclusive(v___x_977_)) as u8;
                    if v_isSharedCheck_1088_ == 0 {
                        v___x_1083_ = v___x_977_;
                        v_isShared_1084_ = v_isSharedCheck_1088_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1081_);
                        crate::leanh::lean_dec(v___x_977_);
                        v___x_1083_ = crate::leanh::lean_box(0);
                        v_isShared_1084_ = v_isSharedCheck_1088_;
                        state = 23;
                        continue;
                    }
                }
            }
            3 => {
                v___x_987_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_988_ = lean_array_get_size(v_a_978_);
                v___x_1009_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
                if v___x_1009_ == 0 {
                    crate::leanh::lean_dec(v_a_973_);
                    crate::leanh::lean_dec_ref(v_f_959_);
                    v___x_1044_ = 1;
                    v___y_990_ = v___x_1044_;
                    state = 6;
                    continue;
                } else {
                    if v___x_1009_ == 0 {
                        crate::leanh::lean_dec(v_a_973_);
                        crate::leanh::lean_dec_ref(v_f_959_);
                        v___y_990_ = v___x_1009_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1045_ = 0usize;
                        v___x_1046_ = lean_usize_of_nat(v___x_988_);
                        v___x_1047_ = (crate::leanh::lean_unbox(v_a_966_) as u8);
                        v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v___x_1047_, v_a_978_, v___x_1045_, v___x_1046_);
                        if v___x_1048_ == 0 {
                            crate::leanh::lean_dec(v_a_973_);
                            crate::leanh::lean_dec_ref(v_f_959_);
                            v___y_990_ = v___x_1009_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_980_);
                            crate::leanh::lean_del_object(v___x_975_);
                            crate::leanh::lean_dec(v_a_966_);
                            if crate::leanh::lean_obj_tag(v_f_959_) == 4 {
                                v_declName_1049_ = crate::leanh::lean_ctor_get(v_f_959_, 0);
                                v_us_1050_ = crate::leanh::lean_ctor_get(v_f_959_, 1);
                                crate::leanh::lean_inc(v_us_1050_);
                                crate::leanh::lean_inc(v_declName_1049_);
                                v___x_1051_ = l_Lean_Meta_mkCongrSimpForConst_x3f(
                                    v_declName_1049_,
                                    v_us_1050_,
                                    v_a_960_,
                                    v_a_961_,
                                    v_a_962_,
                                    v_a_963_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                                    v_a_1052_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                    v_isSharedCheck_1071_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                    if v_isSharedCheck_1071_ == 0 {
                                        v___x_1054_ = v___x_1051_;
                                        v_isShared_1055_ = v_isSharedCheck_1071_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1052_);
                                        crate::leanh::lean_dec(v___x_1051_);
                                        v___x_1054_ = crate::leanh::lean_box(0);
                                        v_isShared_1055_ = v_isSharedCheck_1071_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_f_959_, 2);
                                    crate::leanh::lean_dec(v_a_978_);
                                    crate::leanh::lean_dec(v_a_973_);
                                    v_a_1072_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                    v_isSharedCheck_1079_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                    if v_isSharedCheck_1079_ == 0 {
                                        v___x_1074_ = v___x_1051_;
                                        v_isShared_1075_ = v_isSharedCheck_1079_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1072_);
                                        crate::leanh::lean_dec(v___x_1051_);
                                        v___x_1074_ = crate::leanh::lean_box(0);
                                        v_isShared_1075_ = v_isSharedCheck_1079_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                v___y_1011_ = v_a_960_;
                                v___y_1012_ = v_a_961_;
                                v___y_1013_ = v_a_962_;
                                v___y_1014_ = v_a_963_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_983_ = crate::leanh::lean_box(0);
                if v_isShared_981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_980_, 0, v___x_983_);
                    v___x_985_ = v___x_980_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
                    v___x_985_ = v_reuseFailAlloc_986_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_985_;
            }
            6 => {
                v___x_991_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
                if v___x_991_ == 0 {
                    crate::leanh::lean_dec(v_a_978_);
                    crate::leanh::lean_del_object(v___x_975_);
                    crate::leanh::lean_dec(v_a_966_);
                    state = 4;
                    continue;
                } else {
                    if v___x_991_ == 0 {
                        crate::leanh::lean_dec(v_a_978_);
                        crate::leanh::lean_del_object(v___x_975_);
                        crate::leanh::lean_dec(v_a_966_);
                        state = 4;
                        continue;
                    } else {
                        v___x_992_ = 0usize;
                        v___x_993_ = lean_usize_of_nat(v___x_988_);
                        v___x_994_ = (crate::leanh::lean_unbox(v_a_966_) as u8);
                        crate::leanh::lean_dec(v_a_966_);
                        v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_990_, v___x_994_, v_a_978_, v___x_992_, v___x_993_);
                        if v___x_995_ == 0 {
                            crate::leanh::lean_dec(v_a_978_);
                            crate::leanh::lean_del_object(v___x_975_);
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_980_);
                            v___x_996_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_a_978_);
                            if crate::leanh::lean_obj_tag(v___x_996_) == 1 {
                                crate::leanh::lean_dec(v_a_978_);
                                v_val_997_ = crate::leanh::lean_ctor_get(v___x_996_, 0);
                                crate::leanh::lean_inc(v_val_997_);
                                crate::leanh::lean_dec_ref_known(v___x_996_, 1);
                                v___x_998_ = lean_nat_sub(v___x_988_, v_val_997_);
                                v___x_999_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_999_, 0, v_val_997_);
                                crate::leanh::lean_ctor_set(v___x_999_, 1, v___x_998_);
                                if v_isShared_976_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_999_);
                                    v___x_1001_ = v___x_975_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1002_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1002_,
                                        0,
                                        v___x_999_,
                                    );
                                    v___x_1001_ = v_reuseFailAlloc_1002_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_996_);
                                v_sz_1003_ = lean_array_size(v_a_978_);
                                v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_1003_, v___x_992_, v_a_978_);
                                v___x_1005_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1005_, 0, v___x_1004_);
                                if v_isShared_976_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_1005_);
                                    v___x_1007_ = v___x_975_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1008_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1008_,
                                        0,
                                        v___x_1005_,
                                    );
                                    v___x_1007_ = v_reuseFailAlloc_1008_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            7 => {
                return v___x_1001_;
            }
            8 => {
                return v___x_1007_;
            }
            9 => {
                v___x_1015_ = l_Lean_Meta_mkCongrSimpCore_x3f(
                    v_f_959_,
                    v_a_973_,
                    v_a_978_,
                    v___x_1009_,
                    v___y_1011_,
                    v___y_1012_,
                    v___y_1013_,
                    v___y_1014_,
                );
                if crate::leanh::lean_obj_tag(v___x_1015_) == 0 {
                    v_a_1016_ = crate::leanh::lean_ctor_get(v___x_1015_, 0);
                    v_isSharedCheck_1035_ = (!crate::leanh::lean_is_exclusive(v___x_1015_)) as u8;
                    if v_isSharedCheck_1035_ == 0 {
                        v___x_1018_ = v___x_1015_;
                        v_isShared_1019_ = v_isSharedCheck_1035_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1016_);
                        crate::leanh::lean_dec(v___x_1015_);
                        v___x_1018_ = crate::leanh::lean_box(0);
                        v_isShared_1019_ = v_isSharedCheck_1035_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_1036_ = crate::leanh::lean_ctor_get(v___x_1015_, 0);
                    v_isSharedCheck_1043_ = (!crate::leanh::lean_is_exclusive(v___x_1015_)) as u8;
                    if v_isSharedCheck_1043_ == 0 {
                        v___x_1038_ = v___x_1015_;
                        v_isShared_1039_ = v_isSharedCheck_1043_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1036_);
                        crate::leanh::lean_dec(v___x_1015_);
                        v___x_1038_ = crate::leanh::lean_box(0);
                        v_isShared_1039_ = v_isSharedCheck_1043_;
                        state = 15;
                        continue;
                    }
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_1016_) == 1 {
                    v_val_1020_ = crate::leanh::lean_ctor_get(v_a_1016_, 0);
                    v_isSharedCheck_1030_ = (!crate::leanh::lean_is_exclusive(v_a_1016_)) as u8;
                    if v_isSharedCheck_1030_ == 0 {
                        v___x_1022_ = v_a_1016_;
                        v_isShared_1023_ = v_isSharedCheck_1030_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1020_);
                        crate::leanh::lean_dec(v_a_1016_);
                        v___x_1022_ = crate::leanh::lean_box(0);
                        v_isShared_1023_ = v_isSharedCheck_1030_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1016_);
                    v___x_1031_ = crate::leanh::lean_box(0);
                    if v_isShared_1019_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1018_, 0, v___x_1031_);
                        v___x_1033_ = v___x_1018_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
                        v___x_1033_ = v_reuseFailAlloc_1034_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1023_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1022_, 3);
                    v___x_1025_ = v___x_1022_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1029_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_val_1020_);
                    v___x_1025_ = v_reuseFailAlloc_1029_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1018_, 0, v___x_1025_);
                    v___x_1027_ = v___x_1018_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
                    v___x_1027_ = v_reuseFailAlloc_1028_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1027_;
            }
            14 => {
                return v___x_1033_;
            }
            15 => {
                if v_isShared_1039_ == 0 {
                    v___x_1041_ = v___x_1038_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
                    v___x_1041_ = v_reuseFailAlloc_1042_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1041_;
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_a_1052_) == 1 {
                    v_val_1056_ = crate::leanh::lean_ctor_get(v_a_1052_, 0);
                    v_isSharedCheck_1070_ = (!crate::leanh::lean_is_exclusive(v_a_1052_)) as u8;
                    if v_isSharedCheck_1070_ == 0 {
                        v___x_1058_ = v_a_1052_;
                        v_isShared_1059_ = v_isSharedCheck_1070_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1056_);
                        crate::leanh::lean_dec(v_a_1052_);
                        v___x_1058_ = crate::leanh::lean_box(0);
                        v_isShared_1059_ = v_isSharedCheck_1070_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1054_);
                    crate::leanh::lean_dec(v_a_1052_);
                    v___y_1011_ = v_a_960_;
                    v___y_1012_ = v_a_961_;
                    v___y_1013_ = v_a_962_;
                    v___y_1014_ = v_a_963_;
                    state = 9;
                    continue;
                }
            }
            18 => {
                v_argKinds_1060_ = crate::leanh::lean_ctor_get(v_val_1056_, 2);
                v___x_1061_ = lean_array_get_size(v_argKinds_1060_);
                v___x_1062_ = lean_nat_dec_eq(v___x_1061_, v___x_988_);
                if v___x_1062_ == 0 {
                    crate::leanh::lean_del_object(v___x_1058_);
                    crate::leanh::lean_dec(v_val_1056_);
                    crate::leanh::lean_del_object(v___x_1054_);
                    v___y_1011_ = v_a_960_;
                    v___y_1012_ = v_a_961_;
                    v___y_1013_ = v_a_962_;
                    v___y_1014_ = v_a_963_;
                    state = 9;
                    continue;
                } else {
                    v___x_1063_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_argKinds_1060_, v_a_978_, v___x_1061_);
                    if v___x_1063_ == 0 {
                        crate::leanh::lean_del_object(v___x_1058_);
                        crate::leanh::lean_dec(v_val_1056_);
                        crate::leanh::lean_del_object(v___x_1054_);
                        v___y_1011_ = v_a_960_;
                        v___y_1012_ = v_a_961_;
                        v___y_1013_ = v_a_962_;
                        v___y_1014_ = v_a_963_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_f_959_, 2);
                        crate::leanh::lean_dec(v_a_978_);
                        crate::leanh::lean_dec(v_a_973_);
                        if v_isShared_1059_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1058_, 3);
                            v___x_1065_ = v___x_1058_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_1069_ =
                                crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_val_1056_);
                            v___x_1065_ = v_reuseFailAlloc_1069_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_1055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1054_, 0, v___x_1065_);
                    v___x_1067_ = v___x_1054_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
                    v___x_1067_ = v_reuseFailAlloc_1068_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1067_;
            }
            21 => {
                if v_isShared_1075_ == 0 {
                    v___x_1077_ = v___x_1074_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1077_;
            }
            23 => {
                if v_isShared_1084_ == 0 {
                    v___x_1086_ = v___x_1083_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1086_;
            }
            25 => {
                if v_isShared_1093_ == 0 {
                    v___x_1095_ = v___x_1092_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
                    v___x_1095_ = v_reuseFailAlloc_1096_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1095_;
            }
            27 => {
                return v___x_1100_;
            }
            28 => {
                if v_isShared_1106_ == 0 {
                    v___x_1108_ = v___x_1105_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
                    v___x_1108_ = v_reuseFailAlloc_1109_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(
    mut v_f_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(
        v_f_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_,
    );
    crate::leanh::lean_dec(v_a_1115_);
    crate::leanh::lean_dec_ref(v_a_1114_);
    crate::leanh::lean_dec(v_a_1113_);
    crate::leanh::lean_dec_ref(v_a_1112_);
    return v_res_1117_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(
    mut v_f_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(
        v_f_1118_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_,
    );
    return v___x_1126_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(
    mut v_f_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(
        v_f_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_,
    );
    crate::leanh::lean_dec(v_a_1133_);
    crate::leanh::lean_dec_ref(v_a_1132_);
    crate::leanh::lean_dec(v_a_1131_);
    crate::leanh::lean_dec_ref(v_a_1130_);
    crate::leanh::lean_dec(v_a_1129_);
    crate::leanh::lean_dec_ref(v_a_1128_);
    return v_res_1135_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(
    mut v_xs_1136_: *mut crate::leanh::LeanObject,
    mut v_ys_1137_: *mut crate::leanh::LeanObject,
    mut v_hsz_1138_: *mut crate::leanh::LeanObject,
    mut v_x_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1141_: u8 = 0;
    v___x_1141_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_1136_, v_ys_1137_, v_x_1139_);
    return v___x_1141_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(
    mut v_xs_1142_: *mut crate::leanh::LeanObject,
    mut v_ys_1143_: *mut crate::leanh::LeanObject,
    mut v_hsz_1144_: *mut crate::leanh::LeanObject,
    mut v_x_1145_: *mut crate::leanh::LeanObject,
    mut v_x_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1147_: u8 = 0;
    let mut v_r_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1147_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_xs_1142_, v_ys_1143_, v_hsz_1144_, v_x_1145_, v_x_1146_);
    crate::leanh::lean_dec_ref(v_ys_1143_);
    crate::leanh::lean_dec_ref(v_xs_1142_);
    v_r_1148_ = crate::leanh::lean_box((v_res_1147_) as usize);
    return v_r_1148_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_1149_: *mut crate::leanh::LeanObject,
    mut v_x_1150_: *mut crate::leanh::LeanObject,
    mut v_x_1151_: *mut crate::leanh::LeanObject,
    mut v_x_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1153_ = crate::leanh::lean_ctor_get(v_x_1149_, 0);
                v_vs_1154_ = crate::leanh::lean_ctor_get(v_x_1149_, 1);
                v_isSharedCheck_1178_ = (!crate::leanh::lean_is_exclusive(v_x_1149_)) as u8;
                if v_isSharedCheck_1178_ == 0 {
                    v___x_1156_ = v_x_1149_;
                    v_isShared_1157_ = v_isSharedCheck_1178_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1154_);
                    crate::leanh::lean_inc(v_ks_1153_);
                    crate::leanh::lean_dec(v_x_1149_);
                    v___x_1156_ = crate::leanh::lean_box(0);
                    v_isShared_1157_ = v_isSharedCheck_1178_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1158_ = lean_array_get_size(v_ks_1153_);
                v___x_1159_ = lean_nat_dec_lt(v_x_1150_, v___x_1158_);
                if v___x_1159_ == 0 {
                    crate::leanh::lean_dec(v_x_1150_);
                    v___x_1160_ = lean_array_push(v_ks_1153_, v_x_1151_);
                    v___x_1161_ = lean_array_push(v_vs_1154_, v_x_1152_);
                    if v_isShared_1157_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1156_, 1, v___x_1161_);
                        crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1160_);
                        v___x_1163_ = v___x_1156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1164_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1160_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1161_);
                        v___x_1163_ = v_reuseFailAlloc_1164_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1165_ = lean_array_fget_borrowed(v_ks_1153_, v_x_1150_);
                    v___x_1166_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1151_,
                            v_k_x27_1165_,
                        );
                    if v___x_1166_ == 0 {
                        if v_isShared_1157_ == 0 {
                            v___x_1168_ = v___x_1156_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1172_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_ks_1153_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_vs_1154_);
                            v___x_1168_ = v_reuseFailAlloc_1172_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1173_ = lean_array_fset(v_ks_1153_, v_x_1150_, v_x_1151_);
                        v___x_1174_ = lean_array_fset(v_vs_1154_, v_x_1150_, v_x_1152_);
                        crate::leanh::lean_dec(v_x_1150_);
                        if v_isShared_1157_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1156_, 1, v___x_1174_);
                            crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1173_);
                            v___x_1176_ = v___x_1156_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1177_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1173_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1174_);
                            v___x_1176_ = v_reuseFailAlloc_1177_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1163_;
            }
            3 => {
                v___x_1169_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1170_ = lean_nat_add(v_x_1150_, v___x_1169_);
                crate::leanh::lean_dec(v_x_1150_);
                v_x_1149_ = v___x_1168_;
                v_x_1150_ = v___x_1170_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(
    mut v_n_1179_: *mut crate::leanh::LeanObject,
    mut v_k_1180_: *mut crate::leanh::LeanObject,
    mut v_v_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1183_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1179_, v___x_1182_, v_k_1180_, v_v_1181_);
    return v___x_1183_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1184_: usize = 0;
    let mut v___x_1185_: usize = 0;
    let mut v___x_1186_: usize = 0;
    v___x_1184_ = 5usize;
    v___x_1185_ = 1usize;
    v___x_1186_ = lean_usize_shift_left(v___x_1185_, v___x_1184_);
    return v___x_1186_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1187_: usize = 0;
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: usize = 0;
    v___x_1187_ = 1usize;
    v___x_1188_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0);
    v___x_1189_ = lean_usize_sub(v___x_1188_, v___x_1187_);
    return v___x_1189_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1190_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(
    mut v_x_1191_: *mut crate::leanh::LeanObject,
    mut v_x_1192_: usize,
    mut v_x_1193_: usize,
    mut v_x_1194_: *mut crate::leanh::LeanObject,
    mut v_x_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v___x_1200_: usize = 0;
    let mut v_j_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1206_: u8 = 0;
    let mut v_v_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1221_: u8 = 0;
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut v_node_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1232_: usize = 0;
    let mut v___x_1233_: usize = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut v_unused_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1251_: u8 = 0;
    let mut v_ks_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: usize = 0;
    let mut v___x_1258_: u8 = 0;
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    let mut v_reuseFailAlloc_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1191_) == 0 {
                    v_es_1196_ = crate::leanh::lean_ctor_get(v_x_1191_, 0);
                    v___x_1197_ = 5usize;
                    v___x_1198_ = 1usize;
                    v___x_1199_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1);
                    v___x_1200_ = lean_usize_land(v_x_1192_, v___x_1199_);
                    v_j_1201_ = lean_usize_to_nat(v___x_1200_);
                    v___x_1202_ = lean_array_get_size(v_es_1196_);
                    v___x_1203_ = lean_nat_dec_lt(v_j_1201_, v___x_1202_);
                    if v___x_1203_ == 0 {
                        crate::leanh::lean_dec(v_j_1201_);
                        crate::leanh::lean_dec(v_x_1195_);
                        crate::leanh::lean_dec_ref(v_x_1194_);
                        return v_x_1191_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1196_);
                        v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v_x_1191_)) as u8;
                        if v_isSharedCheck_1240_ == 0 {
                            v_unused_1241_ = crate::leanh::lean_ctor_get(v_x_1191_, 0);
                            crate::leanh::lean_dec(v_unused_1241_);
                            v___x_1205_ = v_x_1191_;
                            v_isShared_1206_ = v_isSharedCheck_1240_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1191_);
                            v___x_1205_ = crate::leanh::lean_box(0);
                            v_isShared_1206_ = v_isSharedCheck_1240_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1242_ = crate::leanh::lean_ctor_get(v_x_1191_, 0);
                    v_vs_1243_ = crate::leanh::lean_ctor_get(v_x_1191_, 1);
                    v_isSharedCheck_1263_ = (!crate::leanh::lean_is_exclusive(v_x_1191_)) as u8;
                    if v_isSharedCheck_1263_ == 0 {
                        v___x_1245_ = v_x_1191_;
                        v_isShared_1246_ = v_isSharedCheck_1263_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1243_);
                        crate::leanh::lean_inc(v_ks_1242_);
                        crate::leanh::lean_dec(v_x_1191_);
                        v___x_1245_ = crate::leanh::lean_box(0);
                        v_isShared_1246_ = v_isSharedCheck_1263_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1207_ = lean_array_fget(v_es_1196_, v_j_1201_);
                v___x_1208_ = crate::leanh::lean_box(0);
                v_xs_x27_1209_ = lean_array_fset(v_es_1196_, v_j_1201_, v___x_1208_);
                match crate::leanh::lean_obj_tag(v_v_1207_) {
                    0 => {
                        v_key_1216_ = crate::leanh::lean_ctor_get(v_v_1207_, 0);
                        v_val_1217_ = crate::leanh::lean_ctor_get(v_v_1207_, 1);
                        v_isSharedCheck_1227_ = (!crate::leanh::lean_is_exclusive(v_v_1207_)) as u8;
                        if v_isSharedCheck_1227_ == 0 {
                            v___x_1219_ = v_v_1207_;
                            v_isShared_1220_ = v_isSharedCheck_1227_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1217_);
                            crate::leanh::lean_inc(v_key_1216_);
                            crate::leanh::lean_dec(v_v_1207_);
                            v___x_1219_ = crate::leanh::lean_box(0);
                            v_isShared_1220_ = v_isSharedCheck_1227_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1228_ = crate::leanh::lean_ctor_get(v_v_1207_, 0);
                        v_isSharedCheck_1238_ = (!crate::leanh::lean_is_exclusive(v_v_1207_)) as u8;
                        if v_isSharedCheck_1238_ == 0 {
                            v___x_1230_ = v_v_1207_;
                            v_isShared_1231_ = v_isSharedCheck_1238_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1228_);
                            crate::leanh::lean_dec(v_v_1207_);
                            v___x_1230_ = crate::leanh::lean_box(0);
                            v_isShared_1231_ = v_isSharedCheck_1238_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1239_, 0, v_x_1194_);
                        crate::leanh::lean_ctor_set(v___x_1239_, 1, v_x_1195_);
                        v___y_1211_ = v___x_1239_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1212_ = lean_array_fset(v_xs_x27_1209_, v_j_1201_, v___y_1211_);
                crate::leanh::lean_dec(v_j_1201_);
                if v_isShared_1206_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1205_, 0, v___x_1212_);
                    v___x_1214_ = v___x_1205_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
                    v___x_1214_ = v_reuseFailAlloc_1215_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1214_;
            }
            4 => {
                v___x_1221_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1194_,
                        v_key_1216_,
                    );
                if v___x_1221_ == 0 {
                    crate::leanh::lean_del_object(v___x_1219_);
                    v___x_1222_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1216_,
                        v_val_1217_,
                        v_x_1194_,
                        v_x_1195_,
                    );
                    v___x_1223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
                    v___y_1211_ = v___x_1223_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1217_);
                    crate::leanh::lean_dec(v_key_1216_);
                    if v_isShared_1220_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1219_, 1, v_x_1195_);
                        crate::leanh::lean_ctor_set(v___x_1219_, 0, v_x_1194_);
                        v___x_1225_ = v___x_1219_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_x_1194_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_x_1195_);
                        v___x_1225_ = v_reuseFailAlloc_1226_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1211_ = v___x_1225_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1232_ = lean_usize_shift_right(v_x_1192_, v___x_1197_);
                v___x_1233_ = lean_usize_add(v_x_1193_, v___x_1198_);
                v___x_1234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_node_1228_, v___x_1232_, v___x_1233_, v_x_1194_, v_x_1195_);
                if v_isShared_1231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1234_);
                    v___x_1236_ = v___x_1230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
                    v___x_1236_ = v_reuseFailAlloc_1237_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1211_ = v___x_1236_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1246_ == 0 {
                    v___x_1248_ = v___x_1245_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_ks_1242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_vs_1243_);
                    v___x_1248_ = v_reuseFailAlloc_1262_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1249_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v___x_1248_, v_x_1194_, v_x_1195_);
                v___x_1257_ = 7usize;
                v___x_1258_ = lean_usize_dec_le(v___x_1257_, v_x_1193_);
                if v___x_1258_ == 0 {
                    v___x_1259_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1249_);
                    v___x_1260_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1261_ = lean_nat_dec_lt(v___x_1259_, v___x_1260_);
                    crate::leanh::lean_dec(v___x_1259_);
                    v___y_1251_ = v___x_1261_;
                    state = 10;
                    continue;
                } else {
                    v___y_1251_ = v___x_1258_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1251_ == 0 {
                    v_ks_1252_ = crate::leanh::lean_ctor_get(v_newNode_1249_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1252_);
                    v_vs_1253_ = crate::leanh::lean_ctor_get(v_newNode_1249_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1253_);
                    crate::leanh::lean_dec_ref(v_newNode_1249_);
                    v___x_1254_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__2);
                    v___x_1256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_x_1193_, v_ks_1252_, v_vs_1253_, v___x_1254_, v___x_1255_);
                    crate::leanh::lean_dec_ref(v_vs_1253_);
                    crate::leanh::lean_dec_ref(v_ks_1252_);
                    return v___x_1256_;
                } else {
                    return v_newNode_1249_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1264_: usize,
    mut v_keys_1265_: *mut crate::leanh::LeanObject,
    mut v_vals_1266_: *mut crate::leanh::LeanObject,
    mut v_i_1267_: *mut crate::leanh::LeanObject,
    mut v_entries_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v_k_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u64 = 0;
    let mut v_h_1274_: usize = 0;
    let mut v___x_1275_: usize = 0;
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: usize = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1279_: usize = 0;
    let mut v_h_1280_: usize = 0;
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = lean_array_get_size(v_keys_1265_);
                v___x_1270_ = lean_nat_dec_lt(v_i_1267_, v___x_1269_);
                if v___x_1270_ == 0 {
                    crate::leanh::lean_dec(v_i_1267_);
                    return v_entries_1268_;
                } else {
                    v_k_1271_ = lean_array_fget_borrowed(v_keys_1265_, v_i_1267_);
                    v_v_1272_ = lean_array_fget_borrowed(v_vals_1266_, v_i_1267_);
                    v___x_1273_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1271_);
                    v_h_1274_ = lean_uint64_to_usize(v___x_1273_);
                    v___x_1275_ = 5usize;
                    v___x_1276_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1277_ = 1usize;
                    v___x_1278_ = lean_usize_sub(v_depth_1264_, v___x_1277_);
                    v___x_1279_ = lean_usize_mul(v___x_1275_, v___x_1278_);
                    v_h_1280_ = lean_usize_shift_right(v_h_1274_, v___x_1279_);
                    v___x_1281_ = lean_nat_add(v_i_1267_, v___x_1276_);
                    crate::leanh::lean_dec(v_i_1267_);
                    crate::leanh::lean_inc(v_v_1272_);
                    crate::leanh::lean_inc(v_k_1271_);
                    v___x_1282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_entries_1268_, v_h_1280_, v_depth_1264_, v_k_1271_, v_v_1272_);
                    v_i_1267_ = v___x_1281_;
                    v_entries_1268_ = v___x_1282_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1284_: *mut crate::leanh::LeanObject,
    mut v_keys_1285_: *mut crate::leanh::LeanObject,
    mut v_vals_1286_: *mut crate::leanh::LeanObject,
    mut v_i_1287_: *mut crate::leanh::LeanObject,
    mut v_entries_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1289_: usize = 0;
    let mut v_res_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1289_ = crate::leanh::lean_unbox_usize(v_depth_1284_);
    crate::leanh::lean_dec(v_depth_1284_);
    v_res_1290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1289_, v_keys_1285_, v_vals_1286_, v_i_1287_, v_entries_1288_);
    crate::leanh::lean_dec_ref(v_vals_1286_);
    crate::leanh::lean_dec_ref(v_keys_1285_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___boxed(
    mut v_x_1291_: *mut crate::leanh::LeanObject,
    mut v_x_1292_: *mut crate::leanh::LeanObject,
    mut v_x_1293_: *mut crate::leanh::LeanObject,
    mut v_x_1294_: *mut crate::leanh::LeanObject,
    mut v_x_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2444__boxed_1296_: usize = 0;
    let mut v_x_2445__boxed_1297_: usize = 0;
    let mut v_res_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2444__boxed_1296_ = crate::leanh::lean_unbox_usize(v_x_1292_);
    crate::leanh::lean_dec(v_x_1292_);
    v_x_2445__boxed_1297_ = crate::leanh::lean_unbox_usize(v_x_1293_);
    crate::leanh::lean_dec(v_x_1293_);
    v_res_1298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_1291_, v_x_2444__boxed_1296_, v_x_2445__boxed_1297_, v_x_1294_, v_x_1295_);
    return v_res_1298_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(
    mut v_x_1299_: *mut crate::leanh::LeanObject,
    mut v_x_1300_: *mut crate::leanh::LeanObject,
    mut v_x_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: u64 = 0;
    let mut v___x_1303_: usize = 0;
    let mut v___x_1304_: usize = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1300_);
    v___x_1303_ = lean_uint64_to_usize(v___x_1302_);
    v___x_1304_ = 1usize;
    v___x_1305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_1299_, v___x_1303_, v___x_1304_, v_x_1300_, v_x_1301_);
    return v___x_1305_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1306_: *mut crate::leanh::LeanObject,
    mut v_vals_1307_: *mut crate::leanh::LeanObject,
    mut v_i_1308_: *mut crate::leanh::LeanObject,
    mut v_k_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = lean_array_get_size(v_keys_1306_);
                v___x_1311_ = lean_nat_dec_lt(v_i_1308_, v___x_1310_);
                if v___x_1311_ == 0 {
                    crate::leanh::lean_dec(v_i_1308_);
                    v___x_1312_ = crate::leanh::lean_box(0);
                    return v___x_1312_;
                } else {
                    v_k_x27_1313_ = lean_array_fget_borrowed(v_keys_1306_, v_i_1308_);
                    v___x_1314_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1309_,
                            v_k_x27_1313_,
                        );
                    if v___x_1314_ == 0 {
                        v___x_1315_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1316_ = lean_nat_add(v_i_1308_, v___x_1315_);
                        crate::leanh::lean_dec(v_i_1308_);
                        v_i_1308_ = v___x_1316_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1318_ = lean_array_fget_borrowed(v_vals_1307_, v_i_1308_);
                        crate::leanh::lean_dec(v_i_1308_);
                        crate::leanh::lean_inc(v___x_1318_);
                        v___x_1319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1318_);
                        return v___x_1319_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1320_: *mut crate::leanh::LeanObject,
    mut v_vals_1321_: *mut crate::leanh::LeanObject,
    mut v_i_1322_: *mut crate::leanh::LeanObject,
    mut v_k_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1324_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_1320_, v_vals_1321_, v_i_1322_, v_k_1323_);
    crate::leanh::lean_dec_ref(v_k_1323_);
    crate::leanh::lean_dec_ref(v_vals_1321_);
    crate::leanh::lean_dec_ref(v_keys_1320_);
    return v_res_1324_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(
    mut v_x_1325_: *mut crate::leanh::LeanObject,
    mut v_x_1326_: usize,
    mut v_x_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: usize = 0;
    let mut v___x_1331_: usize = 0;
    let mut v___x_1332_: usize = 0;
    let mut v_j_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: usize = 0;
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1325_) == 0 {
                    v_es_1328_ = crate::leanh::lean_ctor_get(v_x_1325_, 0);
                    v___x_1329_ = crate::leanh::lean_box(2);
                    v___x_1330_ = 5usize;
                    v___x_1331_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__1);
                    v___x_1332_ = lean_usize_land(v_x_1326_, v___x_1331_);
                    v_j_1333_ = lean_usize_to_nat(v___x_1332_);
                    v___x_1334_ = lean_array_get_borrowed(v___x_1329_, v_es_1328_, v_j_1333_);
                    crate::leanh::lean_dec(v_j_1333_);
                    match crate::leanh::lean_obj_tag(v___x_1334_) {
                        0 => {
                            v_key_1335_ = crate::leanh::lean_ctor_get(v___x_1334_, 0);
                            v_val_1336_ = crate::leanh::lean_ctor_get(v___x_1334_, 1);
                            v___x_1337_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1327_, v_key_1335_);
                            if v___x_1337_ == 0 {
                                v___x_1338_ = crate::leanh::lean_box(0);
                                return v___x_1338_;
                            } else {
                                crate::leanh::lean_inc(v_val_1336_);
                                v___x_1339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1339_, 0, v_val_1336_);
                                return v___x_1339_;
                            }
                        }
                        1 => {
                            v_node_1340_ = crate::leanh::lean_ctor_get(v___x_1334_, 0);
                            v___x_1341_ = lean_usize_shift_right(v_x_1326_, v___x_1330_);
                            v_x_1325_ = v_node_1340_;
                            v_x_1326_ = v___x_1341_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1343_ = crate::leanh::lean_box(0);
                            return v___x_1343_;
                        }
                    }
                } else {
                    v_ks_1344_ = crate::leanh::lean_ctor_get(v_x_1325_, 0);
                    v_vs_1345_ = crate::leanh::lean_ctor_get(v_x_1325_, 1);
                    v___x_1346_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1347_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_ks_1344_, v_vs_1345_, v___x_1346_, v_x_1327_);
                    return v___x_1347_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(
    mut v_x_1348_: *mut crate::leanh::LeanObject,
    mut v_x_1349_: *mut crate::leanh::LeanObject,
    mut v_x_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2644__boxed_1351_: usize = 0;
    let mut v_res_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2644__boxed_1351_ = crate::leanh::lean_unbox_usize(v_x_1349_);
    crate::leanh::lean_dec(v_x_1349_);
    v_res_1352_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_1348_, v_x_2644__boxed_1351_, v_x_1350_);
    crate::leanh::lean_dec_ref(v_x_1350_);
    crate::leanh::lean_dec_ref(v_x_1348_);
    return v_res_1352_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(
    mut v_x_1353_: *mut crate::leanh::LeanObject,
    mut v_x_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: u64 = 0;
    let mut v___x_1356_: usize = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1354_);
    v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
    v___x_1357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_1353_, v___x_1356_, v_x_1354_);
    return v___x_1357_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(
    mut v_x_1358_: *mut crate::leanh::LeanObject,
    mut v_x_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1360_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(
            v_x_1358_, v_x_1359_,
        );
    crate::leanh::lean_dec_ref(v_x_1359_);
    crate::leanh::lean_dec_ref(v_x_1358_);
    return v_res_1360_;
}
pub unsafe fn l_Lean_Meta_Sym_getCongrInfo___redArg(
    mut v_f_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1395_: u8 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1368_ = lean_st_ref_get(v_a_1362_);
                v_congrInfo_1369_ = crate::leanh::lean_ctor_get(v___x_1368_, 5);
                crate::leanh::lean_inc_ref(v_congrInfo_1369_);
                crate::leanh::lean_dec(v___x_1368_);
                v___x_1370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_congrInfo_1369_, v_f_1361_);
                crate::leanh::lean_dec_ref(v_congrInfo_1369_);
                if crate::leanh::lean_obj_tag(v___x_1370_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_1361_);
                    v_val_1371_ = crate::leanh::lean_ctor_get(v___x_1370_, 0);
                    v_isSharedCheck_1378_ = (!crate::leanh::lean_is_exclusive(v___x_1370_)) as u8;
                    if v_isSharedCheck_1378_ == 0 {
                        v___x_1373_ = v___x_1370_;
                        v_isShared_1374_ = v_isSharedCheck_1378_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1371_);
                        crate::leanh::lean_dec(v___x_1370_);
                        v___x_1373_ = crate::leanh::lean_box(0);
                        v_isShared_1374_ = v_isSharedCheck_1378_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1370_);
                    crate::leanh::lean_inc_ref(v_f_1361_);
                    v___x_1379_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
                    if crate::leanh::lean_obj_tag(v___x_1379_) == 0 {
                        v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                        v_isSharedCheck_1408_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1379_)) as u8;
                        if v_isSharedCheck_1408_ == 0 {
                            v___x_1382_ = v___x_1379_;
                            v_isShared_1383_ = v_isSharedCheck_1408_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1380_);
                            crate::leanh::lean_dec(v___x_1379_);
                            v___x_1382_ = crate::leanh::lean_box(0);
                            v_isShared_1383_ = v_isSharedCheck_1408_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_1361_);
                        return v___x_1379_;
                    }
                }
            }
            1 => {
                if v_isShared_1374_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1373_, 0);
                    v___x_1376_ = v___x_1373_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_val_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1376_;
            }
            3 => {
                v___x_1384_ = lean_st_ref_take(v_a_1362_);
                v_share_1385_ = crate::leanh::lean_ctor_get(v___x_1384_, 0);
                v_maxFVar_1386_ = crate::leanh::lean_ctor_get(v___x_1384_, 1);
                v_proofInstInfo_1387_ = crate::leanh::lean_ctor_get(v___x_1384_, 2);
                v_inferType_1388_ = crate::leanh::lean_ctor_get(v___x_1384_, 3);
                v_getLevel_1389_ = crate::leanh::lean_ctor_get(v___x_1384_, 4);
                v_congrInfo_1390_ = crate::leanh::lean_ctor_get(v___x_1384_, 5);
                v_defEqI_1391_ = crate::leanh::lean_ctor_get(v___x_1384_, 6);
                v_extensions_1392_ = crate::leanh::lean_ctor_get(v___x_1384_, 7);
                v_issues_1393_ = crate::leanh::lean_ctor_get(v___x_1384_, 8);
                v_canon_1394_ = crate::leanh::lean_ctor_get(v___x_1384_, 9);
                v_debug_1395_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1384_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1407_ = (!crate::leanh::lean_is_exclusive(v___x_1384_)) as u8;
                if v_isSharedCheck_1407_ == 0 {
                    v___x_1397_ = v___x_1384_;
                    v_isShared_1398_ = v_isSharedCheck_1407_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1394_);
                    crate::leanh::lean_inc(v_issues_1393_);
                    crate::leanh::lean_inc(v_extensions_1392_);
                    crate::leanh::lean_inc(v_defEqI_1391_);
                    crate::leanh::lean_inc(v_congrInfo_1390_);
                    crate::leanh::lean_inc(v_getLevel_1389_);
                    crate::leanh::lean_inc(v_inferType_1388_);
                    crate::leanh::lean_inc(v_proofInstInfo_1387_);
                    crate::leanh::lean_inc(v_maxFVar_1386_);
                    crate::leanh::lean_inc(v_share_1385_);
                    crate::leanh::lean_dec(v___x_1384_);
                    v___x_1397_ = crate::leanh::lean_box(0);
                    v_isShared_1398_ = v_isSharedCheck_1407_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1380_);
                v___x_1399_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_congrInfo_1390_, v_f_1361_, v_a_1380_);
                if v_isShared_1398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1397_, 5, v___x_1399_);
                    v___x_1401_ = v___x_1397_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1406_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_share_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_maxFVar_1386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_proofInstInfo_1387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_inferType_1388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_getLevel_1389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 5, v___x_1399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 6, v_defEqI_1391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 7, v_extensions_1392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 8, v_issues_1393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 9, v_canon_1394_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1406_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1395_,
                    );
                    v___x_1401_ = v_reuseFailAlloc_1406_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1402_ = lean_st_ref_set(v_a_1362_, v___x_1401_);
                if v_isShared_1383_ == 0 {
                    v___x_1404_ = v___x_1382_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1380_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(
    mut v_f_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_Meta_Sym_getCongrInfo___redArg(
        v_f_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_,
    );
    crate::leanh::lean_dec(v_a_1414_);
    crate::leanh::lean_dec_ref(v_a_1413_);
    crate::leanh::lean_dec(v_a_1412_);
    crate::leanh::lean_dec_ref(v_a_1411_);
    crate::leanh::lean_dec(v_a_1410_);
    return v_res_1416_;
}
pub unsafe fn l_Lean_Meta_Sym_getCongrInfo(
    mut v_f_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1425_ = l_Lean_Meta_Sym_getCongrInfo___redArg(
        v_f_1417_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_,
    );
    return v___x_1425_;
}
pub unsafe fn l_Lean_Meta_Sym_getCongrInfo___boxed(
    mut v_f_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_a_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lean_Meta_Sym_getCongrInfo(
        v_f_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_,
    );
    crate::leanh::lean_dec(v_a_1432_);
    crate::leanh::lean_dec_ref(v_a_1431_);
    crate::leanh::lean_dec(v_a_1430_);
    crate::leanh::lean_dec_ref(v_a_1429_);
    crate::leanh::lean_dec(v_a_1428_);
    crate::leanh::lean_dec_ref(v_a_1427_);
    return v_res_1434_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(
    mut v_00_u03b2_1435_: *mut crate::leanh::LeanObject,
    mut v_x_1436_: *mut crate::leanh::LeanObject,
    mut v_x_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(
            v_x_1436_, v_x_1437_,
        );
    return v___x_1438_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(
    mut v_00_u03b2_1439_: *mut crate::leanh::LeanObject,
    mut v_x_1440_: *mut crate::leanh::LeanObject,
    mut v_x_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(
        v_00_u03b2_1439_,
        v_x_1440_,
        v_x_1441_,
    );
    crate::leanh::lean_dec_ref(v_x_1441_);
    crate::leanh::lean_dec_ref(v_x_1440_);
    return v_res_1442_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(
    mut v_00_u03b2_1443_: *mut crate::leanh::LeanObject,
    mut v_x_1444_: *mut crate::leanh::LeanObject,
    mut v_x_1445_: *mut crate::leanh::LeanObject,
    mut v_x_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(
            v_x_1444_, v_x_1445_, v_x_1446_,
        );
    return v___x_1447_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(
    mut v_00_u03b2_1448_: *mut crate::leanh::LeanObject,
    mut v_x_1449_: *mut crate::leanh::LeanObject,
    mut v_x_1450_: usize,
    mut v_x_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_1449_, v_x_1450_, v_x_1451_);
    return v___x_1452_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(
    mut v_00_u03b2_1453_: *mut crate::leanh::LeanObject,
    mut v_x_1454_: *mut crate::leanh::LeanObject,
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2788__boxed_1457_: usize = 0;
    let mut v_res_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2788__boxed_1457_ = crate::leanh::lean_unbox_usize(v_x_1455_);
    crate::leanh::lean_dec(v_x_1455_);
    v_res_1458_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(v_00_u03b2_1453_, v_x_1454_, v_x_2788__boxed_1457_, v_x_1456_);
    crate::leanh::lean_dec_ref(v_x_1456_);
    crate::leanh::lean_dec_ref(v_x_1454_);
    return v_res_1458_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(
    mut v_00_u03b2_1459_: *mut crate::leanh::LeanObject,
    mut v_x_1460_: *mut crate::leanh::LeanObject,
    mut v_x_1461_: usize,
    mut v_x_1462_: usize,
    mut v_x_1463_: *mut crate::leanh::LeanObject,
    mut v_x_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_1460_, v_x_1461_, v_x_1462_, v_x_1463_, v_x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(
    mut v_00_u03b2_1466_: *mut crate::leanh::LeanObject,
    mut v_x_1467_: *mut crate::leanh::LeanObject,
    mut v_x_1468_: *mut crate::leanh::LeanObject,
    mut v_x_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
    mut v_x_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2799__boxed_1472_: usize = 0;
    let mut v_x_2800__boxed_1473_: usize = 0;
    let mut v_res_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2799__boxed_1472_ = crate::leanh::lean_unbox_usize(v_x_1468_);
    crate::leanh::lean_dec(v_x_1468_);
    v_x_2800__boxed_1473_ = crate::leanh::lean_unbox_usize(v_x_1469_);
    crate::leanh::lean_dec(v_x_1469_);
    v_res_1474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(v_00_u03b2_1466_, v_x_1467_, v_x_2799__boxed_1472_, v_x_2800__boxed_1473_, v_x_1470_, v_x_1471_);
    return v_res_1474_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1475_: *mut crate::leanh::LeanObject,
    mut v_keys_1476_: *mut crate::leanh::LeanObject,
    mut v_vals_1477_: *mut crate::leanh::LeanObject,
    mut v_heq_1478_: *mut crate::leanh::LeanObject,
    mut v_i_1479_: *mut crate::leanh::LeanObject,
    mut v_k_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_1476_, v_vals_1477_, v_i_1479_, v_k_1480_);
    return v___x_1481_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1482_: *mut crate::leanh::LeanObject,
    mut v_keys_1483_: *mut crate::leanh::LeanObject,
    mut v_vals_1484_: *mut crate::leanh::LeanObject,
    mut v_heq_1485_: *mut crate::leanh::LeanObject,
    mut v_i_1486_: *mut crate::leanh::LeanObject,
    mut v_k_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(v_00_u03b2_1482_, v_keys_1483_, v_vals_1484_, v_heq_1485_, v_i_1486_, v_k_1487_);
    crate::leanh::lean_dec_ref(v_k_1487_);
    crate::leanh::lean_dec_ref(v_vals_1484_);
    crate::leanh::lean_dec_ref(v_keys_1483_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1489_: *mut crate::leanh::LeanObject,
    mut v_n_1490_: *mut crate::leanh::LeanObject,
    mut v_k_1491_: *mut crate::leanh::LeanObject,
    mut v_v_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v_n_1490_, v_k_1491_, v_v_1492_);
    return v___x_1493_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1494_: *mut crate::leanh::LeanObject,
    mut v_depth_1495_: usize,
    mut v_keys_1496_: *mut crate::leanh::LeanObject,
    mut v_vals_1497_: *mut crate::leanh::LeanObject,
    mut v_heq_1498_: *mut crate::leanh::LeanObject,
    mut v_i_1499_: *mut crate::leanh::LeanObject,
    mut v_entries_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_1495_, v_keys_1496_, v_vals_1497_, v_i_1499_, v_entries_1500_);
    return v___x_1501_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1502_: *mut crate::leanh::LeanObject,
    mut v_depth_1503_: *mut crate::leanh::LeanObject,
    mut v_keys_1504_: *mut crate::leanh::LeanObject,
    mut v_vals_1505_: *mut crate::leanh::LeanObject,
    mut v_heq_1506_: *mut crate::leanh::LeanObject,
    mut v_i_1507_: *mut crate::leanh::LeanObject,
    mut v_entries_1508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1509_: usize = 0;
    let mut v_res_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1509_ = crate::leanh::lean_unbox_usize(v_depth_1503_);
    crate::leanh::lean_dec(v_depth_1503_);
    v_res_1510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(v_00_u03b2_1502_, v_depth_boxed_1509_, v_keys_1504_, v_vals_1505_, v_heq_1506_, v_i_1507_, v_entries_1508_);
    crate::leanh::lean_dec_ref(v_vals_1505_);
    crate::leanh::lean_dec_ref(v_keys_1504_);
    return v_res_1510_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1511_: *mut crate::leanh::LeanObject,
    mut v_x_1512_: *mut crate::leanh::LeanObject,
    mut v_x_1513_: *mut crate::leanh::LeanObject,
    mut v_x_1514_: *mut crate::leanh::LeanObject,
    mut v_x_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1512_, v_x_1513_, v_x_1514_, v_x_1515_);
    return v___x_1516_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___y_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1519_) == 0 {
                    v___x_1521_ = l_List_reverse___redArg(v_a_1520_);
                    return v___x_1521_;
                } else {
                    v_head_1522_ = crate::leanh::lean_ctor_get(v_a_1519_, 0);
                    v_tail_1523_ = crate::leanh::lean_ctor_get(v_a_1519_, 1);
                    v_isSharedCheck_1538_ = (!crate::leanh::lean_is_exclusive(v_a_1519_)) as u8;
                    if v_isSharedCheck_1538_ == 0 {
                        v___x_1525_ = v_a_1519_;
                        v_isShared_1526_ = v_isSharedCheck_1538_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1523_);
                        crate::leanh::lean_inc(v_head_1522_);
                        crate::leanh::lean_dec(v_a_1519_);
                        v___x_1525_ = crate::leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1535_ = (crate::leanh::lean_unbox(v_head_1522_) as u8);
                crate::leanh::lean_dec(v_head_1522_);
                if v___x_1535_ == 0 {
                    v___x_1536_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0;
                    v___y_1528_ = v___x_1536_;
                    state = 2;
                    continue;
                } else {
                    v___x_1537_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1;
                    v___y_1528_ = v___x_1537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_1528_);
                v___x_1529_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1529_, 0, v___y_1528_);
                v___x_1530_ = l_Lean_MessageData_ofFormat(v___x_1529_);
                if v_isShared_1526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1525_, 1, v_a_1520_);
                    crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1530_);
                    v___x_1532_ = v___x_1525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_a_1520_);
                    v___x_1532_ = v_reuseFailAlloc_1534_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_1519_ = v_tail_1523_;
                v_a_1520_ = v___x_1532_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1542_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1;
    v___x_1543_ = l_Lean_MessageData_ofFormat(v___x_1542_);
    return v___x_1543_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3;
    v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
    return v___x_1546_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5;
    v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
    return v___x_1549_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7;
    v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
    return v___x_1552_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9;
    v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
    return v___x_1555_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(
    mut v_x_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prefixSize_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suffixSize_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_rewritable_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1556_) {
                0 => {
                    v___x_1557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2);
                    return v___x_1557_;
                }
                1 => {
                    v_prefixSize_1558_ = crate::leanh::lean_ctor_get(v_x_1556_, 0);
                    v_suffixSize_1559_ = crate::leanh::lean_ctor_get(v_x_1556_, 1);
                    v_isSharedCheck_1576_ = (!crate::leanh::lean_is_exclusive(v_x_1556_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1561_ = v_x_1556_;
                        v_isShared_1562_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_suffixSize_1559_);
                        crate::leanh::lean_inc(v_prefixSize_1558_);
                        crate::leanh::lean_dec(v_x_1556_);
                        v___x_1561_ = crate::leanh::lean_box(0);
                        v_isShared_1562_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_rewritable_1577_ = crate::leanh::lean_ctor_get(v_x_1556_, 0);
                    crate::leanh::lean_inc_ref(v_rewritable_1577_);
                    crate::leanh::lean_dec_ref_known(v_x_1556_, 1);
                    v___x_1578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once), _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8);
                    v___x_1579_ = lean_array_to_list(v_rewritable_1577_);
                    v___x_1580_ = crate::leanh::lean_box(0);
                    v___x_1581_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(v___x_1579_, v___x_1580_);
                    v___x_1582_ = l_Lean_MessageData_ofList(v___x_1581_);
                    v___x_1583_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1578_);
                    crate::leanh::lean_ctor_set(v___x_1583_, 1, v___x_1582_);
                    return v___x_1583_;
                }
                _ => {
                    v_thm_1584_ = crate::leanh::lean_ctor_get(v_x_1556_, 0);
                    crate::leanh::lean_inc_ref(v_thm_1584_);
                    crate::leanh::lean_dec_ref_known(v_x_1556_, 1);
                    v_proof_1585_ = crate::leanh::lean_ctor_get(v_thm_1584_, 1);
                    crate::leanh::lean_inc_ref(v_proof_1585_);
                    crate::leanh::lean_dec_ref(v_thm_1584_);
                    v___x_1586_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once), _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10);
                    v___x_1587_ = l_Lean_MessageData_ofExpr(v_proof_1585_);
                    v___x_1588_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1588_, 0, v___x_1586_);
                    crate::leanh::lean_ctor_set(v___x_1588_, 1, v___x_1587_);
                    return v___x_1588_;
                }
            },
            1 => {
                v___x_1563_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once), _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4);
                v___x_1564_ = l_Nat_reprFast(v_prefixSize_1558_);
                v___x_1565_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
                v___x_1566_ = l_Lean_MessageData_ofFormat(v___x_1565_);
                if v_isShared_1562_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1561_, 7);
                    crate::leanh::lean_ctor_set(v___x_1561_, 1, v___x_1566_);
                    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1563_);
                    v___x_1568_ = v___x_1561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1566_);
                    v___x_1568_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1569_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once), _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6);
                v___x_1570_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1568_);
                crate::leanh::lean_ctor_set(v___x_1570_, 1, v___x_1569_);
                v___x_1571_ = l_Nat_reprFast(v_suffixSize_1559_);
                v___x_1572_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1572_, 0, v___x_1571_);
                v___x_1573_ = l_Lean_MessageData_ofFormat(v___x_1572_);
                v___x_1574_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1574_, 0, v___x_1570_);
                crate::leanh::lean_ctor_set(v___x_1574_, 1, v___x_1573_);
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_CongrInfo(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_CongrInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
}
