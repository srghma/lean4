// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Model
// Imports: Init.Data.Array.TakeDrop Std.Data.DHashMap.Basic Std.Data.DHashMap.Internal.Defs Std.Data.DHashMap.Internal.HashesTo Std.Data.DHashMap.Internal.AssocList.Lemmas Init.Data.Array.Bootstrap Init.Data.UInt.Lemmas
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::TakeDrop::{
    initialize_Init_Data_Array_TakeDrop, runtime_initialize_Init_Data_Array_TakeDrop,
};
use crate::r#gen::Init::Data::List::Control::l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DHashMap::Basic::{
    initialize_Std_Data_DHashMap_Basic, runtime_initialize_Std_Data_DHashMap_Basic,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    l_Std_DHashMap_Internal_AssocList_Const_alter___redArg,
    l_Std_DHashMap_Internal_AssocList_alter___redArg,
    l_Std_DHashMap_Internal_AssocList_contains___redArg,
    l_Std_DHashMap_Internal_AssocList_erase___redArg,
    l_Std_DHashMap_Internal_AssocList_get___redArg,
    l_Std_DHashMap_Internal_AssocList_get_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getCast___redArg,
    l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntry___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntryD___redArg,
    l_Std_DHashMap_Internal_AssocList_getKey___redArg,
    l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_length___redArg,
    l_Std_DHashMap_Internal_AssocList_replace___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Lemmas::{
    initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas,
    runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    initialize_Std_Data_DHashMap_Internal_Defs, l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_toListModel___redArg,
    runtime_initialize_Std_Data_DHashMap_Internal_Defs,
};
use crate::r#gen::Std::Data::DHashMap::Internal::HashesTo::{
    initialize_Std_Data_DHashMap_Internal_HashesTo,
    runtime_initialize_Std_Data_DHashMap_Internal_HashesTo,
};
pub static l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_bucket___redArg(
    mut v_inst_1548_: *mut leanh::LeanObject,
    mut v_self_1549_: *mut leanh::LeanObject,
    mut v_k_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: u64 = 0;
    let mut v___x_1554_: u64 = 0;
    let mut v___x_1555_: u64 = 0;
    let mut v___x_1556_: u64 = 0;
    let mut v_fold_1557_: u64 = 0;
    let mut v___x_1558_: u64 = 0;
    let mut v___x_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: usize = 0;
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = lean_array_get_size(v_self_1549_);
    v___x_1552_ = leanh::lean_apply_1(v_inst_1548_, v_k_1550_);
    v___x_1553_ = 32u64;
    v___x_1554_ = leanh::lean_unbox_uint64(v___x_1552_);
    v___x_1555_ = lean_uint64_shift_right(v___x_1554_, v___x_1553_);
    v___x_1556_ = leanh::lean_unbox_uint64(v___x_1552_);
    leanh::lean_dec_ref(v___x_1552_);
    v_fold_1557_ = lean_uint64_xor(v___x_1556_, v___x_1555_);
    v___x_1558_ = 16u64;
    v___x_1559_ = lean_uint64_shift_right(v_fold_1557_, v___x_1558_);
    v___x_1560_ = lean_uint64_xor(v_fold_1557_, v___x_1559_);
    v___x_1561_ = lean_uint64_to_usize(v___x_1560_);
    v___x_1562_ = lean_usize_of_nat(v___x_1551_);
    v___x_1563_ = 1usize;
    v___x_1564_ = lean_usize_sub(v___x_1562_, v___x_1563_);
    v___x_1565_ = lean_usize_land(v___x_1561_, v___x_1564_);
    v___x_1566_ = lean_array_uget_borrowed(v_self_1549_, v___x_1565_);
    leanh::lean_inc(v___x_1566_);
    return v___x_1566_;
}
pub unsafe fn l_Std_DHashMap_Internal_bucket___redArg___boxed(
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_self_1568_: *mut leanh::LeanObject,
    mut v_k_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1567_, v_self_1568_, v_k_1569_);
    leanh::lean_dec_ref(v_self_1568_);
    return v_res_1570_;
}
pub unsafe fn l_Std_DHashMap_Internal_bucket(
    mut v_00_u03b1_1571_: *mut leanh::LeanObject,
    mut v_00_u03b2_1572_: *mut leanh::LeanObject,
    mut v_inst_1573_: *mut leanh::LeanObject,
    mut v_self_1574_: *mut leanh::LeanObject,
    mut v_h_1575_: *mut leanh::LeanObject,
    mut v_k_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1573_, v_self_1574_, v_k_1576_);
    return v___x_1577_;
}
pub unsafe fn l_Std_DHashMap_Internal_bucket___boxed(
    mut v_00_u03b1_1578_: *mut leanh::LeanObject,
    mut v_00_u03b2_1579_: *mut leanh::LeanObject,
    mut v_inst_1580_: *mut leanh::LeanObject,
    mut v_self_1581_: *mut leanh::LeanObject,
    mut v_h_1582_: *mut leanh::LeanObject,
    mut v_k_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Std_DHashMap_Internal_bucket(
        v_00_u03b1_1578_,
        v_00_u03b2_1579_,
        v_inst_1580_,
        v_self_1581_,
        v_h_1582_,
        v_k_1583_,
    );
    leanh::lean_dec_ref(v_self_1581_);
    return v_res_1584_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateBucket___redArg(
    mut v_inst_1585_: *mut leanh::LeanObject,
    mut v_self_1586_: *mut leanh::LeanObject,
    mut v_k_1587_: *mut leanh::LeanObject,
    mut v_f_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: u64 = 0;
    let mut v___x_1592_: u64 = 0;
    let mut v___x_1593_: u64 = 0;
    let mut v___x_1594_: u64 = 0;
    let mut v_fold_1595_: u64 = 0;
    let mut v___x_1596_: u64 = 0;
    let mut v___x_1597_: u64 = 0;
    let mut v___x_1598_: u64 = 0;
    let mut v___x_1599_: usize = 0;
    let mut v___x_1600_: usize = 0;
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: usize = 0;
    let mut v___x_1603_: usize = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = lean_array_get_size(v_self_1586_);
    v___x_1590_ = leanh::lean_apply_1(v_inst_1585_, v_k_1587_);
    v___x_1591_ = 32u64;
    v___x_1592_ = leanh::lean_unbox_uint64(v___x_1590_);
    v___x_1593_ = lean_uint64_shift_right(v___x_1592_, v___x_1591_);
    v___x_1594_ = leanh::lean_unbox_uint64(v___x_1590_);
    leanh::lean_dec_ref(v___x_1590_);
    v_fold_1595_ = lean_uint64_xor(v___x_1594_, v___x_1593_);
    v___x_1596_ = 16u64;
    v___x_1597_ = lean_uint64_shift_right(v_fold_1595_, v___x_1596_);
    v___x_1598_ = lean_uint64_xor(v_fold_1595_, v___x_1597_);
    v___x_1599_ = lean_uint64_to_usize(v___x_1598_);
    v___x_1600_ = lean_usize_of_nat(v___x_1589_);
    v___x_1601_ = 1usize;
    v___x_1602_ = lean_usize_sub(v___x_1600_, v___x_1601_);
    v___x_1603_ = lean_usize_land(v___x_1599_, v___x_1602_);
    v___x_1604_ = lean_array_uget_borrowed(v_self_1586_, v___x_1603_);
    leanh::lean_inc(v___x_1604_);
    v___x_1605_ = leanh::lean_apply_1(v_f_1588_, v___x_1604_);
    v___x_1606_ = lean_array_uset(v_self_1586_, v___x_1603_, v___x_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateBucket(
    mut v_00_u03b1_1607_: *mut leanh::LeanObject,
    mut v_00_u03b2_1608_: *mut leanh::LeanObject,
    mut v_inst_1609_: *mut leanh::LeanObject,
    mut v_self_1610_: *mut leanh::LeanObject,
    mut v_h_1611_: *mut leanh::LeanObject,
    mut v_k_1612_: *mut leanh::LeanObject,
    mut v_f_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Std_DHashMap_Internal_updateBucket___redArg(
        v_inst_1609_,
        v_self_1610_,
        v_k_1612_,
        v_f_1613_,
    );
    return v___x_1614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(
    mut v_f_1615_: *mut leanh::LeanObject,
    mut v_sz_1616_: usize,
    mut v_i_1617_: usize,
    mut v_bs_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1619_: u8 = 0;
    let mut v_v_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: usize = 0;
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1619_ = lean_usize_dec_lt(v_i_1617_, v_sz_1616_);
                if v___x_1619_ == 0 {
                    leanh::lean_dec_ref(v_f_1615_);
                    return v_bs_1618_;
                } else {
                    v_v_1620_ = lean_array_uget(v_bs_1618_, v_i_1617_);
                    v___x_1621_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1622_ = lean_array_uset(v_bs_1618_, v_i_1617_, v___x_1621_);
                    leanh::lean_inc_ref(v_f_1615_);
                    v___x_1623_ = leanh::lean_apply_1(v_f_1615_, v_v_1620_);
                    v___x_1624_ = 1usize;
                    v___x_1625_ = lean_usize_add(v_i_1617_, v___x_1624_);
                    v___x_1626_ = lean_array_uset(v_bs_x27_1622_, v_i_1617_, v___x_1623_);
                    v_i_1617_ = v___x_1625_;
                    v_bs_1618_ = v___x_1626_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg___boxed(
    mut v_f_1628_: *mut leanh::LeanObject,
    mut v_sz_1629_: *mut leanh::LeanObject,
    mut v_i_1630_: *mut leanh::LeanObject,
    mut v_bs_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1632_: usize = 0;
    let mut v_i_boxed_1633_: usize = 0;
    let mut v_res_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1632_ = leanh::lean_unbox_usize(v_sz_1629_);
    leanh::lean_dec(v_sz_1629_);
    v_i_boxed_1633_ = leanh::lean_unbox_usize(v_i_1630_);
    leanh::lean_dec(v_i_1630_);
    v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_1628_, v_sz_boxed_1632_, v_i_boxed_1633_, v_bs_1631_);
    return v_res_1634_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateAllBuckets___redArg(
    mut v_self_1635_: *mut leanh::LeanObject,
    mut v_f_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1637_: usize = 0;
    let mut v___x_1638_: usize = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1637_ = lean_array_size(v_self_1635_);
    v___x_1638_ = 0usize;
    v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_1636_, v_sz_1637_, v___x_1638_, v_self_1635_);
    return v___x_1639_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateAllBuckets(
    mut v_00_u03b1_1640_: *mut leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut leanh::LeanObject,
    mut v_00_u03b4_1642_: *mut leanh::LeanObject,
    mut v_self_1643_: *mut leanh::LeanObject,
    mut v_f_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_self_1643_, v_f_1644_);
    return v___x_1645_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(
    mut v_00_u03b1_1646_: *mut leanh::LeanObject,
    mut v_00_u03b2_1647_: *mut leanh::LeanObject,
    mut v_00_u03b4_1648_: *mut leanh::LeanObject,
    mut v_f_1649_: *mut leanh::LeanObject,
    mut v_sz_1650_: usize,
    mut v_i_1651_: usize,
    mut v_bs_1652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_1649_, v_sz_1650_, v_i_1651_, v_bs_1652_);
    return v___x_1653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___boxed(
    mut v_00_u03b1_1654_: *mut leanh::LeanObject,
    mut v_00_u03b2_1655_: *mut leanh::LeanObject,
    mut v_00_u03b4_1656_: *mut leanh::LeanObject,
    mut v_f_1657_: *mut leanh::LeanObject,
    mut v_sz_1658_: *mut leanh::LeanObject,
    mut v_i_1659_: *mut leanh::LeanObject,
    mut v_bs_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1661_: usize = 0;
    let mut v_i_boxed_1662_: usize = 0;
    let mut v_res_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1661_ = leanh::lean_unbox_usize(v_sz_1658_);
    leanh::lean_dec(v_sz_1658_);
    v_i_boxed_1662_ = leanh::lean_unbox_usize(v_i_1659_);
    leanh::lean_dec(v_i_1659_);
    v_res_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(v_00_u03b1_1654_, v_00_u03b2_1655_, v_00_u03b4_1656_, v_f_1657_, v_sz_boxed_1661_, v_i_boxed_1662_, v_bs_1660_);
    return v_res_1663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(
    mut v_as_1664_: *mut leanh::LeanObject,
    mut v_i_1665_: usize,
    mut v_stop_1666_: usize,
    mut v_b_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: usize = 0;
    let mut v___x_1673_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1668_ = lean_usize_dec_eq(v_i_1665_, v_stop_1666_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = lean_array_uget_borrowed(v_as_1664_, v_i_1665_);
                    v___x_1670_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_1669_);
                    v___x_1671_ = lean_nat_add(v_b_1667_, v___x_1670_);
                    leanh::lean_dec(v___x_1670_);
                    leanh::lean_dec(v_b_1667_);
                    v___x_1672_ = 1usize;
                    v___x_1673_ = lean_usize_add(v_i_1665_, v___x_1672_);
                    v_i_1665_ = v___x_1673_;
                    v_b_1667_ = v___x_1671_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1667_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg___boxed(
    mut v_as_1675_: *mut leanh::LeanObject,
    mut v_i_1676_: *mut leanh::LeanObject,
    mut v_stop_1677_: *mut leanh::LeanObject,
    mut v_b_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1679_: usize = 0;
    let mut v_stop_boxed_1680_: usize = 0;
    let mut v_res_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1679_ = leanh::lean_unbox_usize(v_i_1676_);
    leanh::lean_dec(v_i_1676_);
    v_stop_boxed_1680_ = leanh::lean_unbox_usize(v_stop_1677_);
    leanh::lean_dec(v_stop_1677_);
    v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_1675_, v_i_boxed_1679_, v_stop_boxed_1680_, v_b_1678_);
    leanh::lean_dec_ref(v_as_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Std_DHashMap_Internal_withComputedSize___redArg(
    mut v_self_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v___x_1683_ = leanh::lean_unsigned_to_nat(0);
    v___x_1684_ = lean_array_get_size(v_self_1682_);
    v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
    if v___x_1685_ == 0 {
        let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1686_, 0, v___x_1683_);
        leanh::lean_ctor_set(v___x_1686_, 1, v_self_1682_);
        return v___x_1686_;
    } else {
        let mut v___x_1687_: u8 = 0;
        v___x_1687_ = lean_nat_dec_le(v___x_1684_, v___x_1684_);
        if v___x_1687_ == 0 {
            if v___x_1685_ == 0 {
                let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1688_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1688_, 0, v___x_1683_);
                leanh::lean_ctor_set(v___x_1688_, 1, v_self_1682_);
                return v___x_1688_;
            } else {
                let mut v___x_1689_: usize = 0;
                let mut v___x_1690_: usize = 0;
                let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1689_ = 0usize;
                v___x_1690_ = lean_usize_of_nat(v___x_1684_);
                v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_1682_, v___x_1689_, v___x_1690_, v___x_1683_);
                v___x_1692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                leanh::lean_ctor_set(v___x_1692_, 1, v_self_1682_);
                return v___x_1692_;
            }
        } else {
            let mut v___x_1693_: usize = 0;
            let mut v___x_1694_: usize = 0;
            let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1693_ = 0usize;
            v___x_1694_ = lean_usize_of_nat(v___x_1684_);
            v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_1682_, v___x_1693_, v___x_1694_, v___x_1683_);
            v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
            leanh::lean_ctor_set(v___x_1696_, 1, v_self_1682_);
            return v___x_1696_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_withComputedSize(
    mut v_00_u03b1_1697_: *mut leanh::LeanObject,
    mut v_00_u03b2_1698_: *mut leanh::LeanObject,
    mut v_self_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_self_1699_);
    return v___x_1700_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(
    mut v_00_u03b1_1701_: *mut leanh::LeanObject,
    mut v_00_u03b2_1702_: *mut leanh::LeanObject,
    mut v_as_1703_: *mut leanh::LeanObject,
    mut v_i_1704_: usize,
    mut v_stop_1705_: usize,
    mut v_b_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_1703_, v_i_1704_, v_stop_1705_, v_b_1706_);
    return v___x_1707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___boxed(
    mut v_00_u03b1_1708_: *mut leanh::LeanObject,
    mut v_00_u03b2_1709_: *mut leanh::LeanObject,
    mut v_as_1710_: *mut leanh::LeanObject,
    mut v_i_1711_: *mut leanh::LeanObject,
    mut v_stop_1712_: *mut leanh::LeanObject,
    mut v_b_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1714_: usize = 0;
    let mut v_stop_boxed_1715_: usize = 0;
    let mut v_res_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1714_ = leanh::lean_unbox_usize(v_i_1711_);
    leanh::lean_dec(v_i_1711_);
    v_stop_boxed_1715_ = leanh::lean_unbox_usize(v_stop_1712_);
    leanh::lean_dec(v_stop_1712_);
    v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(v_00_u03b1_1708_, v_00_u03b2_1709_, v_as_1710_, v_i_boxed_1714_, v_stop_boxed_1715_, v_b_1713_);
    leanh::lean_dec_ref(v_as_1710_);
    return v_res_1716_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0(
    mut v_inst_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
    mut v_b_1719_: *mut leanh::LeanObject,
    mut v_l_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
        v_inst_1717_,
        v_a_1718_,
        v_b_1719_,
        v_l_1720_,
    );
    return v___x_1721_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(
    mut v_inst_1722_: *mut leanh::LeanObject,
    mut v_inst_1723_: *mut leanh::LeanObject,
    mut v_m_1724_: *mut leanh::LeanObject,
    mut v_a_1725_: *mut leanh::LeanObject,
    mut v_b_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___f_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1727_ = leanh::lean_ctor_get(v_m_1724_, 0);
                v_buckets_1728_ = leanh::lean_ctor_get(v_m_1724_, 1);
                v_isSharedCheck_1737_ = (!leanh::lean_is_exclusive(v_m_1724_)) as u8;
                if v_isSharedCheck_1737_ == 0 {
                    v___x_1730_ = v_m_1724_;
                    v_isShared_1731_ = v_isSharedCheck_1737_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1728_);
                    leanh::lean_inc(v_size_1727_);
                    leanh::lean_dec(v_m_1724_);
                    v___x_1730_ = leanh::lean_box(0);
                    v_isShared_1731_ = v_isSharedCheck_1737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_1725_);
                v___f_1732_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1732_, 0, v_inst_1722_);
                leanh::lean_closure_set(v___f_1732_, 1, v_a_1725_);
                leanh::lean_closure_set(v___f_1732_, 2, v_b_1726_);
                v___x_1733_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_1723_,
                    v_buckets_1728_,
                    v_a_1725_,
                    v___f_1732_,
                );
                if v_isShared_1731_ == 0 {
                    leanh::lean_ctor_set(v___x_1730_, 1, v___x_1733_);
                    v___x_1735_ = v___x_1730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_size_1727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1733_);
                    v___x_1735_ = v_reuseFailAlloc_1736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(
    mut v_00_u03b1_1738_: *mut leanh::LeanObject,
    mut v_00_u03b2_1739_: *mut leanh::LeanObject,
    mut v_inst_1740_: *mut leanh::LeanObject,
    mut v_inst_1741_: *mut leanh::LeanObject,
    mut v_m_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
    mut v_b_1744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(
        v_inst_1740_,
        v_inst_1741_,
        v_m_1742_,
        v_a_1743_,
        v_b_1744_,
    );
    return v___x_1745_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0(
    mut v_a_1746_: *mut leanh::LeanObject,
    mut v_b_1747_: *mut leanh::LeanObject,
    mut v_l_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1749_, 0, v_a_1746_);
    leanh::lean_ctor_set(v___x_1749_, 1, v_b_1747_);
    leanh::lean_ctor_set(v___x_1749_, 2, v_l_1748_);
    return v___x_1749_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_m_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_b_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___f_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1754_ = leanh::lean_ctor_get(v_m_1751_, 0);
                v_buckets_1755_ = leanh::lean_ctor_get(v_m_1751_, 1);
                v_isSharedCheck_1766_ = (!leanh::lean_is_exclusive(v_m_1751_)) as u8;
                if v_isSharedCheck_1766_ == 0 {
                    v___x_1757_ = v_m_1751_;
                    v_isShared_1758_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1755_);
                    leanh::lean_inc(v_size_1754_);
                    leanh::lean_dec(v_m_1751_);
                    v___x_1757_ = leanh::lean_box(0);
                    v_isShared_1758_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_1752_);
                v___f_1759_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1759_, 0, v_a_1752_);
                leanh::lean_closure_set(v___f_1759_, 1, v_b_1753_);
                v___x_1760_ = leanh::lean_unsigned_to_nat(1);
                v___x_1761_ = lean_nat_add(v_size_1754_, v___x_1760_);
                leanh::lean_dec(v_size_1754_);
                v___x_1762_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_1750_,
                    v_buckets_1755_,
                    v_a_1752_,
                    v___f_1759_,
                );
                if v_isShared_1758_ == 0 {
                    leanh::lean_ctor_set(v___x_1757_, 1, v___x_1762_);
                    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1761_);
                    v___x_1764_ = v___x_1757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
                    v___x_1764_ = v_reuseFailAlloc_1765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(
    mut v_00_u03b1_1767_: *mut leanh::LeanObject,
    mut v_00_u03b2_1768_: *mut leanh::LeanObject,
    mut v_inst_1769_: *mut leanh::LeanObject,
    mut v_inst_1770_: *mut leanh::LeanObject,
    mut v_m_1771_: *mut leanh::LeanObject,
    mut v_a_1772_: *mut leanh::LeanObject,
    mut v_b_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
        v_inst_1770_,
        v_m_1771_,
        v_a_1772_,
        v_b_1773_,
    );
    return v___x_1774_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___boxed(
    mut v_00_u03b1_1775_: *mut leanh::LeanObject,
    mut v_00_u03b2_1776_: *mut leanh::LeanObject,
    mut v_inst_1777_: *mut leanh::LeanObject,
    mut v_inst_1778_: *mut leanh::LeanObject,
    mut v_m_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
    mut v_b_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(
        v_00_u03b1_1775_,
        v_00_u03b2_1776_,
        v_inst_1777_,
        v_inst_1778_,
        v_m_1779_,
        v_a_1780_,
        v_b_1781_,
    );
    leanh::lean_dec_ref(v_inst_1777_);
    return v_res_1782_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
    mut v_inst_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_m_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1787_ = leanh::lean_ctor_get(v_m_1785_, 1);
    leanh::lean_inc(v_a_1786_);
    v___x_1788_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1784_, v_buckets_1787_, v_a_1786_);
    v___x_1789_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
        v_inst_1783_,
        v_a_1786_,
        v___x_1788_,
    );
    return v___x_1789_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(
    mut v_inst_1790_: *mut leanh::LeanObject,
    mut v_inst_1791_: *mut leanh::LeanObject,
    mut v_m_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_1790_,
        v_inst_1791_,
        v_m_1792_,
        v_a_1793_,
    );
    leanh::lean_dec_ref(v_m_1792_);
    return v_res_1794_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(
    mut v_00_u03b1_1795_: *mut leanh::LeanObject,
    mut v_00_u03b2_1796_: *mut leanh::LeanObject,
    mut v_inst_1797_: *mut leanh::LeanObject,
    mut v_inst_1798_: *mut leanh::LeanObject,
    mut v_inst_1799_: *mut leanh::LeanObject,
    mut v_m_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_1797_,
        v_inst_1799_,
        v_m_1800_,
        v_a_1801_,
    );
    return v___x_1802_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(
    mut v_00_u03b1_1803_: *mut leanh::LeanObject,
    mut v_00_u03b2_1804_: *mut leanh::LeanObject,
    mut v_inst_1805_: *mut leanh::LeanObject,
    mut v_inst_1806_: *mut leanh::LeanObject,
    mut v_inst_1807_: *mut leanh::LeanObject,
    mut v_m_1808_: *mut leanh::LeanObject,
    mut v_a_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(
        v_00_u03b1_1803_,
        v_00_u03b2_1804_,
        v_inst_1805_,
        v_inst_1806_,
        v_inst_1807_,
        v_m_1808_,
        v_a_1809_,
    );
    leanh::lean_dec_ref(v_m_1808_);
    return v_res_1810_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
    mut v_inst_1811_: *mut leanh::LeanObject,
    mut v_inst_1812_: *mut leanh::LeanObject,
    mut v_m_1813_: *mut leanh::LeanObject,
    mut v_a_1814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1815_ = leanh::lean_ctor_get(v_m_1813_, 1);
    leanh::lean_inc(v_a_1814_);
    v___x_1816_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1812_, v_buckets_1815_, v_a_1814_);
    v___x_1817_ =
        l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_1811_, v_a_1814_, v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(
    mut v_inst_1818_: *mut leanh::LeanObject,
    mut v_inst_1819_: *mut leanh::LeanObject,
    mut v_m_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_1818_,
        v_inst_1819_,
        v_m_1820_,
        v_a_1821_,
    );
    leanh::lean_dec_ref(v_m_1820_);
    return v_res_1822_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(
    mut v_00_u03b1_1823_: *mut leanh::LeanObject,
    mut v_00_u03b2_1824_: *mut leanh::LeanObject,
    mut v_inst_1825_: *mut leanh::LeanObject,
    mut v_inst_1826_: *mut leanh::LeanObject,
    mut v_m_1827_: *mut leanh::LeanObject,
    mut v_a_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_1825_,
        v_inst_1826_,
        v_m_1827_,
        v_a_1828_,
    );
    return v___x_1829_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(
    mut v_00_u03b1_1830_: *mut leanh::LeanObject,
    mut v_00_u03b2_1831_: *mut leanh::LeanObject,
    mut v_inst_1832_: *mut leanh::LeanObject,
    mut v_inst_1833_: *mut leanh::LeanObject,
    mut v_m_1834_: *mut leanh::LeanObject,
    mut v_a_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1836_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(
        v_00_u03b1_1830_,
        v_00_u03b2_1831_,
        v_inst_1832_,
        v_inst_1833_,
        v_m_1834_,
        v_a_1835_,
    );
    leanh::lean_dec_ref(v_m_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
    mut v_inst_1837_: *mut leanh::LeanObject,
    mut v_inst_1838_: *mut leanh::LeanObject,
    mut v_m_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    v_buckets_1841_ = leanh::lean_ctor_get(v_m_1839_, 1);
    leanh::lean_inc(v_a_1840_);
    v___x_1842_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1838_, v_buckets_1841_, v_a_1840_);
    v___x_1843_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1837_, v_a_1840_, v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(
    mut v_inst_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_m_1846_: *mut leanh::LeanObject,
    mut v_a_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: u8 = 0;
    let mut v_r_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
        v_inst_1844_,
        v_inst_1845_,
        v_m_1846_,
        v_a_1847_,
    );
    leanh::lean_dec_ref(v_m_1846_);
    v_r_1849_ = leanh::lean_box((v_res_1848_) as usize);
    return v_r_1849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(
    mut v_00_u03b1_1850_: *mut leanh::LeanObject,
    mut v_00_u03b2_1851_: *mut leanh::LeanObject,
    mut v_inst_1852_: *mut leanh::LeanObject,
    mut v_inst_1853_: *mut leanh::LeanObject,
    mut v_m_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1856_: u8 = 0;
    v___x_1856_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
        v_inst_1852_,
        v_inst_1853_,
        v_m_1854_,
        v_a_1855_,
    );
    return v___x_1856_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___boxed(
    mut v_00_u03b1_1857_: *mut leanh::LeanObject,
    mut v_00_u03b2_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_inst_1860_: *mut leanh::LeanObject,
    mut v_m_1861_: *mut leanh::LeanObject,
    mut v_a_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1863_: u8 = 0;
    let mut v_r_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(
        v_00_u03b1_1857_,
        v_00_u03b2_1858_,
        v_inst_1859_,
        v_inst_1860_,
        v_m_1861_,
        v_a_1862_,
    );
    leanh::lean_dec_ref(v_m_1861_);
    v_r_1864_ = leanh::lean_box((v_res_1863_) as usize);
    return v_r_1864_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(
    mut v_inst_1865_: *mut leanh::LeanObject,
    mut v_inst_1866_: *mut leanh::LeanObject,
    mut v_m_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1869_ = leanh::lean_ctor_get(v_m_1867_, 1);
    leanh::lean_inc(v_a_1868_);
    v___x_1870_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1866_, v_buckets_1869_, v_a_1868_);
    v___x_1871_ =
        l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1865_, v_a_1868_, v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_inst_1873_: *mut leanh::LeanObject,
    mut v_m_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(
        v_inst_1872_,
        v_inst_1873_,
        v_m_1874_,
        v_a_1875_,
    );
    leanh::lean_dec_ref(v_m_1874_);
    return v_res_1876_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098(
    mut v_00_u03b1_1877_: *mut leanh::LeanObject,
    mut v_00_u03b2_1878_: *mut leanh::LeanObject,
    mut v_inst_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_inst_1881_: *mut leanh::LeanObject,
    mut v_m_1882_: *mut leanh::LeanObject,
    mut v_a_1883_: *mut leanh::LeanObject,
    mut v_h_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(
        v_inst_1879_,
        v_inst_1881_,
        v_m_1882_,
        v_a_1883_,
    );
    return v___x_1885_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(
    mut v_00_u03b1_1886_: *mut leanh::LeanObject,
    mut v_00_u03b2_1887_: *mut leanh::LeanObject,
    mut v_inst_1888_: *mut leanh::LeanObject,
    mut v_inst_1889_: *mut leanh::LeanObject,
    mut v_inst_1890_: *mut leanh::LeanObject,
    mut v_m_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
    mut v_h_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098(
        v_00_u03b1_1886_,
        v_00_u03b2_1887_,
        v_inst_1888_,
        v_inst_1889_,
        v_inst_1890_,
        v_m_1891_,
        v_a_1892_,
        v_h_1893_,
    );
    leanh::lean_dec_ref(v_m_1891_);
    return v_res_1894_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(
    mut v_inst_1895_: *mut leanh::LeanObject,
    mut v_inst_1896_: *mut leanh::LeanObject,
    mut v_m_1897_: *mut leanh::LeanObject,
    mut v_a_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1899_ = leanh::lean_ctor_get(v_m_1897_, 1);
    leanh::lean_inc(v_a_1898_);
    v___x_1900_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1896_, v_buckets_1899_, v_a_1898_);
    v___x_1901_ =
        l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1895_, v_a_1898_, v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(
    mut v_inst_1902_: *mut leanh::LeanObject,
    mut v_inst_1903_: *mut leanh::LeanObject,
    mut v_m_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(
        v_inst_1902_,
        v_inst_1903_,
        v_m_1904_,
        v_a_1905_,
    );
    leanh::lean_dec_ref(v_m_1904_);
    return v_res_1906_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(
    mut v_00_u03b1_1907_: *mut leanh::LeanObject,
    mut v_00_u03b2_1908_: *mut leanh::LeanObject,
    mut v_inst_1909_: *mut leanh::LeanObject,
    mut v_inst_1910_: *mut leanh::LeanObject,
    mut v_m_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
    mut v_h_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(
        v_inst_1909_,
        v_inst_1910_,
        v_m_1911_,
        v_a_1912_,
    );
    return v___x_1914_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(
    mut v_00_u03b1_1915_: *mut leanh::LeanObject,
    mut v_00_u03b2_1916_: *mut leanh::LeanObject,
    mut v_inst_1917_: *mut leanh::LeanObject,
    mut v_inst_1918_: *mut leanh::LeanObject,
    mut v_m_1919_: *mut leanh::LeanObject,
    mut v_a_1920_: *mut leanh::LeanObject,
    mut v_h_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(
        v_00_u03b1_1915_,
        v_00_u03b2_1916_,
        v_inst_1917_,
        v_inst_1918_,
        v_m_1919_,
        v_a_1920_,
        v_h_1921_,
    );
    leanh::lean_dec_ref(v_m_1919_);
    return v_res_1922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
    mut v_inst_1923_: *mut leanh::LeanObject,
    mut v_inst_1924_: *mut leanh::LeanObject,
    mut v_m_1925_: *mut leanh::LeanObject,
    mut v_a_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1927_ = leanh::lean_ctor_get(v_m_1925_, 1);
    leanh::lean_inc(v_a_1926_);
    v___x_1928_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1924_, v_buckets_1927_, v_a_1926_);
    v___x_1929_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(
        v_inst_1923_,
        v_a_1926_,
        v___x_1928_,
    );
    return v___x_1929_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(
    mut v_inst_1930_: *mut leanh::LeanObject,
    mut v_inst_1931_: *mut leanh::LeanObject,
    mut v_m_1932_: *mut leanh::LeanObject,
    mut v_a_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
        v_inst_1930_,
        v_inst_1931_,
        v_m_1932_,
        v_a_1933_,
    );
    leanh::lean_dec_ref(v_m_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(
    mut v_00_u03b1_1935_: *mut leanh::LeanObject,
    mut v_00_u03b2_1936_: *mut leanh::LeanObject,
    mut v_inst_1937_: *mut leanh::LeanObject,
    mut v_inst_1938_: *mut leanh::LeanObject,
    mut v_m_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
        v_inst_1937_,
        v_inst_1938_,
        v_m_1939_,
        v_a_1940_,
    );
    return v___x_1941_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(
    mut v_00_u03b1_1942_: *mut leanh::LeanObject,
    mut v_00_u03b2_1943_: *mut leanh::LeanObject,
    mut v_inst_1944_: *mut leanh::LeanObject,
    mut v_inst_1945_: *mut leanh::LeanObject,
    mut v_m_1946_: *mut leanh::LeanObject,
    mut v_a_1947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(
        v_00_u03b1_1942_,
        v_00_u03b2_1943_,
        v_inst_1944_,
        v_inst_1945_,
        v_m_1946_,
        v_a_1947_,
    );
    leanh::lean_dec_ref(v_m_1946_);
    return v_res_1948_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(
    mut v_inst_1949_: *mut leanh::LeanObject,
    mut v_inst_1950_: *mut leanh::LeanObject,
    mut v_m_1951_: *mut leanh::LeanObject,
    mut v_a_1952_: *mut leanh::LeanObject,
    mut v_fallback_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1954_ = leanh::lean_ctor_get(v_m_1951_, 1);
    leanh::lean_inc(v_a_1952_);
    v___x_1955_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1950_, v_buckets_1954_, v_a_1952_);
    v___x_1956_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1949_,
        v_a_1952_,
        v_fallback_1953_,
        v___x_1955_,
    );
    return v___x_1956_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg___boxed(
    mut v_inst_1957_: *mut leanh::LeanObject,
    mut v_inst_1958_: *mut leanh::LeanObject,
    mut v_m_1959_: *mut leanh::LeanObject,
    mut v_a_1960_: *mut leanh::LeanObject,
    mut v_fallback_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(
        v_inst_1957_,
        v_inst_1958_,
        v_m_1959_,
        v_a_1960_,
        v_fallback_1961_,
    );
    leanh::lean_dec_ref(v_fallback_1961_);
    leanh::lean_dec_ref(v_m_1959_);
    return v_res_1962_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(
    mut v_00_u03b1_1963_: *mut leanh::LeanObject,
    mut v_00_u03b2_1964_: *mut leanh::LeanObject,
    mut v_inst_1965_: *mut leanh::LeanObject,
    mut v_inst_1966_: *mut leanh::LeanObject,
    mut v_m_1967_: *mut leanh::LeanObject,
    mut v_a_1968_: *mut leanh::LeanObject,
    mut v_fallback_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(
        v_inst_1965_,
        v_inst_1966_,
        v_m_1967_,
        v_a_1968_,
        v_fallback_1969_,
    );
    return v___x_1970_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___boxed(
    mut v_00_u03b1_1971_: *mut leanh::LeanObject,
    mut v_00_u03b2_1972_: *mut leanh::LeanObject,
    mut v_inst_1973_: *mut leanh::LeanObject,
    mut v_inst_1974_: *mut leanh::LeanObject,
    mut v_m_1975_: *mut leanh::LeanObject,
    mut v_a_1976_: *mut leanh::LeanObject,
    mut v_fallback_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1978_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(
        v_00_u03b1_1971_,
        v_00_u03b2_1972_,
        v_inst_1973_,
        v_inst_1974_,
        v_m_1975_,
        v_a_1976_,
        v_fallback_1977_,
    );
    leanh::lean_dec_ref(v_fallback_1977_);
    leanh::lean_dec_ref(v_m_1975_);
    return v_res_1978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(
    mut v_inst_1979_: *mut leanh::LeanObject,
    mut v_inst_1980_: *mut leanh::LeanObject,
    mut v_inst_1981_: *mut leanh::LeanObject,
    mut v_m_1982_: *mut leanh::LeanObject,
    mut v_a_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1984_ = leanh::lean_ctor_get(v_m_1982_, 1);
    leanh::lean_inc(v_a_1983_);
    v___x_1985_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1980_, v_buckets_1984_, v_a_1983_);
    v___x_1986_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1979_,
        v_a_1983_,
        v_inst_1981_,
        v___x_1985_,
    );
    return v___x_1986_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg___boxed(
    mut v_inst_1987_: *mut leanh::LeanObject,
    mut v_inst_1988_: *mut leanh::LeanObject,
    mut v_inst_1989_: *mut leanh::LeanObject,
    mut v_m_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(
        v_inst_1987_,
        v_inst_1988_,
        v_inst_1989_,
        v_m_1990_,
        v_a_1991_,
    );
    leanh::lean_dec_ref(v_m_1990_);
    leanh::lean_dec_ref(v_inst_1989_);
    return v_res_1992_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(
    mut v_00_u03b1_1993_: *mut leanh::LeanObject,
    mut v_00_u03b2_1994_: *mut leanh::LeanObject,
    mut v_inst_1995_: *mut leanh::LeanObject,
    mut v_inst_1996_: *mut leanh::LeanObject,
    mut v_inst_1997_: *mut leanh::LeanObject,
    mut v_m_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(
        v_inst_1995_,
        v_inst_1996_,
        v_inst_1997_,
        v_m_1998_,
        v_a_1999_,
    );
    return v___x_2000_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___boxed(
    mut v_00_u03b1_2001_: *mut leanh::LeanObject,
    mut v_00_u03b2_2002_: *mut leanh::LeanObject,
    mut v_inst_2003_: *mut leanh::LeanObject,
    mut v_inst_2004_: *mut leanh::LeanObject,
    mut v_inst_2005_: *mut leanh::LeanObject,
    mut v_m_2006_: *mut leanh::LeanObject,
    mut v_a_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2008_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(
        v_00_u03b1_2001_,
        v_00_u03b2_2002_,
        v_inst_2003_,
        v_inst_2004_,
        v_inst_2005_,
        v_m_2006_,
        v_a_2007_,
    );
    leanh::lean_dec_ref(v_m_2006_);
    leanh::lean_dec_ref(v_inst_2005_);
    return v_res_2008_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(
    mut v_inst_2009_: *mut leanh::LeanObject,
    mut v_inst_2010_: *mut leanh::LeanObject,
    mut v_m_2011_: *mut leanh::LeanObject,
    mut v_a_2012_: *mut leanh::LeanObject,
    mut v_fallback_2013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_2009_,
        v_inst_2010_,
        v_m_2011_,
        v_a_2012_,
    );
    if leanh::lean_obj_tag(v___x_2014_) == 0 {
        leanh::lean_inc(v_fallback_2013_);
        return v_fallback_2013_;
    } else {
        let mut v_val_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2015_ = leanh::lean_ctor_get(v___x_2014_, 0);
        leanh::lean_inc(v_val_2015_);
        leanh::lean_dec_ref_known(v___x_2014_, 1);
        return v_val_2015_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(
    mut v_inst_2016_: *mut leanh::LeanObject,
    mut v_inst_2017_: *mut leanh::LeanObject,
    mut v_m_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
    mut v_fallback_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(
        v_inst_2016_,
        v_inst_2017_,
        v_m_2018_,
        v_a_2019_,
        v_fallback_2020_,
    );
    leanh::lean_dec(v_fallback_2020_);
    leanh::lean_dec_ref(v_m_2018_);
    return v_res_2021_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(
    mut v_00_u03b1_2022_: *mut leanh::LeanObject,
    mut v_00_u03b2_2023_: *mut leanh::LeanObject,
    mut v_inst_2024_: *mut leanh::LeanObject,
    mut v_inst_2025_: *mut leanh::LeanObject,
    mut v_inst_2026_: *mut leanh::LeanObject,
    mut v_m_2027_: *mut leanh::LeanObject,
    mut v_a_2028_: *mut leanh::LeanObject,
    mut v_fallback_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(
        v_inst_2024_,
        v_inst_2026_,
        v_m_2027_,
        v_a_2028_,
        v_fallback_2029_,
    );
    return v___x_2030_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___boxed(
    mut v_00_u03b1_2031_: *mut leanh::LeanObject,
    mut v_00_u03b2_2032_: *mut leanh::LeanObject,
    mut v_inst_2033_: *mut leanh::LeanObject,
    mut v_inst_2034_: *mut leanh::LeanObject,
    mut v_inst_2035_: *mut leanh::LeanObject,
    mut v_m_2036_: *mut leanh::LeanObject,
    mut v_a_2037_: *mut leanh::LeanObject,
    mut v_fallback_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(
        v_00_u03b1_2031_,
        v_00_u03b2_2032_,
        v_inst_2033_,
        v_inst_2034_,
        v_inst_2035_,
        v_m_2036_,
        v_a_2037_,
        v_fallback_2038_,
    );
    leanh::lean_dec(v_fallback_2038_);
    leanh::lean_dec_ref(v_m_2036_);
    return v_res_2039_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2;
    v___x_2044_ = leanh::lean_unsigned_to_nat(14);
    v___x_2045_ = leanh::lean_unsigned_to_nat(22);
    v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1;
    v___x_2047_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0;
    v___x_2048_ = l_mkPanicMessageWithDecl(
        v___x_2047_,
        v___x_2046_,
        v___x_2045_,
        v___x_2044_,
        v___x_2043_,
    );
    return v___x_2048_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(
    mut v_inst_2049_: *mut leanh::LeanObject,
    mut v_inst_2050_: *mut leanh::LeanObject,
    mut v_m_2051_: *mut leanh::LeanObject,
    mut v_a_2052_: *mut leanh::LeanObject,
    mut v_inst_2053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_2049_,
        v_inst_2050_,
        v_m_2051_,
        v_a_2052_,
    );
    if leanh::lean_obj_tag(v___x_2054_) == 0 {
        let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2055_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3,
        );
        v___x_2056_ = l_panic___redArg(v_inst_2053_, v___x_2055_);
        return v___x_2056_;
    } else {
        let mut v_val_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2057_ = leanh::lean_ctor_get(v___x_2054_, 0);
        leanh::lean_inc(v_val_2057_);
        leanh::lean_dec_ref_known(v___x_2054_, 1);
        return v_val_2057_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(
    mut v_inst_2058_: *mut leanh::LeanObject,
    mut v_inst_2059_: *mut leanh::LeanObject,
    mut v_m_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
    mut v_inst_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(
        v_inst_2058_,
        v_inst_2059_,
        v_m_2060_,
        v_a_2061_,
        v_inst_2062_,
    );
    leanh::lean_dec(v_inst_2062_);
    leanh::lean_dec_ref(v_m_2060_);
    return v_res_2063_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(
    mut v_00_u03b1_2064_: *mut leanh::LeanObject,
    mut v_00_u03b2_2065_: *mut leanh::LeanObject,
    mut v_inst_2066_: *mut leanh::LeanObject,
    mut v_inst_2067_: *mut leanh::LeanObject,
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v_m_2069_: *mut leanh::LeanObject,
    mut v_a_2070_: *mut leanh::LeanObject,
    mut v_inst_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(
        v_inst_2066_,
        v_inst_2068_,
        v_m_2069_,
        v_a_2070_,
        v_inst_2071_,
    );
    return v___x_2072_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___boxed(
    mut v_00_u03b1_2073_: *mut leanh::LeanObject,
    mut v_00_u03b2_2074_: *mut leanh::LeanObject,
    mut v_inst_2075_: *mut leanh::LeanObject,
    mut v_inst_2076_: *mut leanh::LeanObject,
    mut v_inst_2077_: *mut leanh::LeanObject,
    mut v_m_2078_: *mut leanh::LeanObject,
    mut v_a_2079_: *mut leanh::LeanObject,
    mut v_inst_2080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2081_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(
        v_00_u03b1_2073_,
        v_00_u03b2_2074_,
        v_inst_2075_,
        v_inst_2076_,
        v_inst_2077_,
        v_m_2078_,
        v_a_2079_,
        v_inst_2080_,
    );
    leanh::lean_dec(v_inst_2080_);
    leanh::lean_dec_ref(v_m_2078_);
    return v_res_2081_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(
    mut v_inst_2082_: *mut leanh::LeanObject,
    mut v_inst_2083_: *mut leanh::LeanObject,
    mut v_m_2084_: *mut leanh::LeanObject,
    mut v_a_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2086_ = leanh::lean_ctor_get(v_m_2084_, 1);
    leanh::lean_inc(v_a_2085_);
    v___x_2087_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_2083_, v_buckets_2086_, v_a_2085_);
    v___x_2088_ =
        l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_2082_, v_a_2085_, v___x_2087_);
    return v___x_2088_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(
    mut v_inst_2089_: *mut leanh::LeanObject,
    mut v_inst_2090_: *mut leanh::LeanObject,
    mut v_m_2091_: *mut leanh::LeanObject,
    mut v_a_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(
        v_inst_2089_,
        v_inst_2090_,
        v_m_2091_,
        v_a_2092_,
    );
    leanh::lean_dec_ref(v_m_2091_);
    return v_res_2093_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(
    mut v_00_u03b1_2094_: *mut leanh::LeanObject,
    mut v_00_u03b2_2095_: *mut leanh::LeanObject,
    mut v_inst_2096_: *mut leanh::LeanObject,
    mut v_inst_2097_: *mut leanh::LeanObject,
    mut v_m_2098_: *mut leanh::LeanObject,
    mut v_a_2099_: *mut leanh::LeanObject,
    mut v_h_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(
        v_inst_2096_,
        v_inst_2097_,
        v_m_2098_,
        v_a_2099_,
    );
    return v___x_2101_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(
    mut v_00_u03b1_2102_: *mut leanh::LeanObject,
    mut v_00_u03b2_2103_: *mut leanh::LeanObject,
    mut v_inst_2104_: *mut leanh::LeanObject,
    mut v_inst_2105_: *mut leanh::LeanObject,
    mut v_m_2106_: *mut leanh::LeanObject,
    mut v_a_2107_: *mut leanh::LeanObject,
    mut v_h_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(
        v_00_u03b1_2102_,
        v_00_u03b2_2103_,
        v_inst_2104_,
        v_inst_2105_,
        v_m_2106_,
        v_a_2107_,
        v_h_2108_,
    );
    leanh::lean_dec_ref(v_m_2106_);
    return v_res_2109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(
    mut v_inst_2110_: *mut leanh::LeanObject,
    mut v_inst_2111_: *mut leanh::LeanObject,
    mut v_m_2112_: *mut leanh::LeanObject,
    mut v_a_2113_: *mut leanh::LeanObject,
    mut v_fallback_2114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_2110_,
        v_inst_2111_,
        v_m_2112_,
        v_a_2113_,
    );
    if leanh::lean_obj_tag(v___x_2115_) == 0 {
        leanh::lean_inc(v_fallback_2114_);
        return v_fallback_2114_;
    } else {
        let mut v_val_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2116_ = leanh::lean_ctor_get(v___x_2115_, 0);
        leanh::lean_inc(v_val_2116_);
        leanh::lean_dec_ref_known(v___x_2115_, 1);
        return v_val_2116_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(
    mut v_inst_2117_: *mut leanh::LeanObject,
    mut v_inst_2118_: *mut leanh::LeanObject,
    mut v_m_2119_: *mut leanh::LeanObject,
    mut v_a_2120_: *mut leanh::LeanObject,
    mut v_fallback_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(
        v_inst_2117_,
        v_inst_2118_,
        v_m_2119_,
        v_a_2120_,
        v_fallback_2121_,
    );
    leanh::lean_dec(v_fallback_2121_);
    leanh::lean_dec_ref(v_m_2119_);
    return v_res_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(
    mut v_00_u03b1_2123_: *mut leanh::LeanObject,
    mut v_00_u03b2_2124_: *mut leanh::LeanObject,
    mut v_inst_2125_: *mut leanh::LeanObject,
    mut v_inst_2126_: *mut leanh::LeanObject,
    mut v_m_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
    mut v_fallback_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(
        v_inst_2125_,
        v_inst_2126_,
        v_m_2127_,
        v_a_2128_,
        v_fallback_2129_,
    );
    return v___x_2130_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___boxed(
    mut v_00_u03b1_2131_: *mut leanh::LeanObject,
    mut v_00_u03b2_2132_: *mut leanh::LeanObject,
    mut v_inst_2133_: *mut leanh::LeanObject,
    mut v_inst_2134_: *mut leanh::LeanObject,
    mut v_m_2135_: *mut leanh::LeanObject,
    mut v_a_2136_: *mut leanh::LeanObject,
    mut v_fallback_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(
        v_00_u03b1_2131_,
        v_00_u03b2_2132_,
        v_inst_2133_,
        v_inst_2134_,
        v_m_2135_,
        v_a_2136_,
        v_fallback_2137_,
    );
    leanh::lean_dec(v_fallback_2137_);
    leanh::lean_dec_ref(v_m_2135_);
    return v_res_2138_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(
    mut v_inst_2139_: *mut leanh::LeanObject,
    mut v_inst_2140_: *mut leanh::LeanObject,
    mut v_inst_2141_: *mut leanh::LeanObject,
    mut v_m_2142_: *mut leanh::LeanObject,
    mut v_a_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_2139_,
        v_inst_2140_,
        v_m_2142_,
        v_a_2143_,
    );
    if leanh::lean_obj_tag(v___x_2144_) == 0 {
        let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2145_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3,
        );
        v___x_2146_ = l_panic___redArg(v_inst_2141_, v___x_2145_);
        return v___x_2146_;
    } else {
        let mut v_val_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2147_ = leanh::lean_ctor_get(v___x_2144_, 0);
        leanh::lean_inc(v_val_2147_);
        leanh::lean_dec_ref_known(v___x_2144_, 1);
        return v_val_2147_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(
    mut v_inst_2148_: *mut leanh::LeanObject,
    mut v_inst_2149_: *mut leanh::LeanObject,
    mut v_inst_2150_: *mut leanh::LeanObject,
    mut v_m_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(
        v_inst_2148_,
        v_inst_2149_,
        v_inst_2150_,
        v_m_2151_,
        v_a_2152_,
    );
    leanh::lean_dec_ref(v_m_2151_);
    leanh::lean_dec(v_inst_2150_);
    return v_res_2153_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(
    mut v_00_u03b1_2154_: *mut leanh::LeanObject,
    mut v_00_u03b2_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_inst_2157_: *mut leanh::LeanObject,
    mut v_inst_2158_: *mut leanh::LeanObject,
    mut v_m_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(
        v_inst_2156_,
        v_inst_2157_,
        v_inst_2158_,
        v_m_2159_,
        v_a_2160_,
    );
    return v___x_2161_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___boxed(
    mut v_00_u03b1_2162_: *mut leanh::LeanObject,
    mut v_00_u03b2_2163_: *mut leanh::LeanObject,
    mut v_inst_2164_: *mut leanh::LeanObject,
    mut v_inst_2165_: *mut leanh::LeanObject,
    mut v_inst_2166_: *mut leanh::LeanObject,
    mut v_m_2167_: *mut leanh::LeanObject,
    mut v_a_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(
        v_00_u03b1_2162_,
        v_00_u03b2_2163_,
        v_inst_2164_,
        v_inst_2165_,
        v_inst_2166_,
        v_m_2167_,
        v_a_2168_,
    );
    leanh::lean_dec_ref(v_m_2167_);
    leanh::lean_dec(v_inst_2166_);
    return v_res_2169_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(
    mut v_inst_2170_: *mut leanh::LeanObject,
    mut v_inst_2171_: *mut leanh::LeanObject,
    mut v_m_2172_: *mut leanh::LeanObject,
    mut v_a_2173_: *mut leanh::LeanObject,
    mut v_b_2174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2175_: u8 = 0;
    let mut v_val_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v_val_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_unused_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2173_);
                leanh::lean_inc_ref(v_inst_2171_);
                leanh::lean_inc_ref(v_inst_2170_);
                v___x_2175_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2170_,
                    v_inst_2171_,
                    v_m_2172_,
                    v_a_2173_,
                );
                if v___x_2175_ == 0 {
                    leanh::lean_dec_ref(v_inst_2170_);
                    leanh::lean_inc_ref(v_inst_2171_);
                    v_val_2176_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                        v_inst_2171_,
                        v_m_2172_,
                        v_a_2173_,
                        v_b_2174_,
                    );
                    v_size_2177_ = leanh::lean_ctor_get(v_val_2176_, 0);
                    leanh::lean_inc(v_size_2177_);
                    v_buckets_2178_ = leanh::lean_ctor_get(v_val_2176_, 1);
                    leanh::lean_inc_ref(v_buckets_2178_);
                    v___x_2179_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2180_ = lean_nat_mul(v_size_2177_, v___x_2179_);
                    v___x_2181_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2182_ = lean_nat_div(v___x_2180_, v___x_2181_);
                    leanh::lean_dec(v___x_2180_);
                    v___x_2183_ = lean_array_get_size(v_buckets_2178_);
                    v___x_2184_ = lean_nat_dec_le(v___x_2182_, v___x_2183_);
                    leanh::lean_dec(v___x_2182_);
                    if v___x_2184_ == 0 {
                        v_isSharedCheck_2192_ =
                            (!leanh::lean_is_exclusive(v_val_2176_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v_unused_2193_ = leanh::lean_ctor_get(v_val_2176_, 1);
                            leanh::lean_dec(v_unused_2193_);
                            v_unused_2194_ = leanh::lean_ctor_get(v_val_2176_, 0);
                            leanh::lean_dec(v_unused_2194_);
                            v___x_2186_ = v_val_2176_;
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_2176_);
                            v___x_2186_ = leanh::lean_box(0);
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_buckets_2178_);
                        leanh::lean_dec(v_size_2177_);
                        leanh::lean_dec_ref(v_inst_2171_);
                        return v_val_2176_;
                    }
                } else {
                    v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(
                        v_inst_2170_,
                        v_inst_2171_,
                        v_m_2172_,
                        v_a_2173_,
                        v_b_2174_,
                    );
                    return v___x_2195_;
                }
            }
            1 => {
                v_val_2188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2171_,
                    v_buckets_2178_,
                );
                if v_isShared_2187_ == 0 {
                    leanh::lean_ctor_set(v___x_2186_, 1, v_val_2188_);
                    v___x_2190_ = v___x_2186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_2177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_val_2188_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert_u2098(
    mut v_00_u03b1_2196_: *mut leanh::LeanObject,
    mut v_00_u03b2_2197_: *mut leanh::LeanObject,
    mut v_inst_2198_: *mut leanh::LeanObject,
    mut v_inst_2199_: *mut leanh::LeanObject,
    mut v_m_2200_: *mut leanh::LeanObject,
    mut v_a_2201_: *mut leanh::LeanObject,
    mut v_b_2202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(
        v_inst_2198_,
        v_inst_2199_,
        v_m_2200_,
        v_a_2201_,
        v_b_2202_,
    );
    return v___x_2203_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(
    mut v_inst_2204_: *mut leanh::LeanObject,
    mut v_inst_2205_: *mut leanh::LeanObject,
    mut v_m_2206_: *mut leanh::LeanObject,
    mut v_a_2207_: *mut leanh::LeanObject,
    mut v_b_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2209_: u8 = 0;
    let mut v_val_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v_val_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut v_unused_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2207_);
                leanh::lean_inc_ref(v_inst_2205_);
                v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2204_,
                    v_inst_2205_,
                    v_m_2206_,
                    v_a_2207_,
                );
                if v___x_2209_ == 0 {
                    leanh::lean_inc_ref(v_inst_2205_);
                    v_val_2210_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                        v_inst_2205_,
                        v_m_2206_,
                        v_a_2207_,
                        v_b_2208_,
                    );
                    v_size_2211_ = leanh::lean_ctor_get(v_val_2210_, 0);
                    leanh::lean_inc(v_size_2211_);
                    v_buckets_2212_ = leanh::lean_ctor_get(v_val_2210_, 1);
                    leanh::lean_inc_ref(v_buckets_2212_);
                    v___x_2213_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2214_ = lean_nat_mul(v_size_2211_, v___x_2213_);
                    v___x_2215_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2216_ = lean_nat_div(v___x_2214_, v___x_2215_);
                    leanh::lean_dec(v___x_2214_);
                    v___x_2217_ = lean_array_get_size(v_buckets_2212_);
                    v___x_2218_ = lean_nat_dec_le(v___x_2216_, v___x_2217_);
                    leanh::lean_dec(v___x_2216_);
                    if v___x_2218_ == 0 {
                        v_isSharedCheck_2226_ =
                            (!leanh::lean_is_exclusive(v_val_2210_)) as u8;
                        if v_isSharedCheck_2226_ == 0 {
                            v_unused_2227_ = leanh::lean_ctor_get(v_val_2210_, 1);
                            leanh::lean_dec(v_unused_2227_);
                            v_unused_2228_ = leanh::lean_ctor_get(v_val_2210_, 0);
                            leanh::lean_dec(v_unused_2228_);
                            v___x_2220_ = v_val_2210_;
                            v_isShared_2221_ = v_isSharedCheck_2226_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_2210_);
                            v___x_2220_ = leanh::lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2226_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_buckets_2212_);
                        leanh::lean_dec(v_size_2211_);
                        leanh::lean_dec_ref(v_inst_2205_);
                        return v_val_2210_;
                    }
                } else {
                    leanh::lean_dec(v_b_2208_);
                    leanh::lean_dec(v_a_2207_);
                    leanh::lean_dec_ref(v_inst_2205_);
                    return v_m_2206_;
                }
            }
            1 => {
                v_val_2222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2205_,
                    v_buckets_2212_,
                );
                if v_isShared_2221_ == 0 {
                    leanh::lean_ctor_set(v___x_2220_, 1, v_val_2222_);
                    v___x_2224_ = v___x_2220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_size_2211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_val_2222_);
                    v___x_2224_ = v_reuseFailAlloc_2225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098(
    mut v_00_u03b1_2229_: *mut leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut leanh::LeanObject,
    mut v_inst_2231_: *mut leanh::LeanObject,
    mut v_inst_2232_: *mut leanh::LeanObject,
    mut v_m_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_b_2235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(
        v_inst_2231_,
        v_inst_2232_,
        v_m_2233_,
        v_a_2234_,
        v_b_2235_,
    );
    return v___x_2236_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0(
    mut v_inst_2237_: *mut leanh::LeanObject,
    mut v_a_2238_: *mut leanh::LeanObject,
    mut v_l_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ =
        l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_2237_, v_a_2238_, v_l_2239_);
    return v___x_2240_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(
    mut v_inst_2241_: *mut leanh::LeanObject,
    mut v_inst_2242_: *mut leanh::LeanObject,
    mut v_m_2243_: *mut leanh::LeanObject,
    mut v_a_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2249_: u8 = 0;
    let mut v___f_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2245_ = leanh::lean_ctor_get(v_m_2243_, 0);
                v_buckets_2246_ = leanh::lean_ctor_get(v_m_2243_, 1);
                v_isSharedCheck_2257_ = (!leanh::lean_is_exclusive(v_m_2243_)) as u8;
                if v_isSharedCheck_2257_ == 0 {
                    v___x_2248_ = v_m_2243_;
                    v_isShared_2249_ = v_isSharedCheck_2257_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2246_);
                    leanh::lean_inc(v_size_2245_);
                    leanh::lean_dec(v_m_2243_);
                    v___x_2248_ = leanh::lean_box(0);
                    v_isShared_2249_ = v_isSharedCheck_2257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_2244_);
                v___f_2250_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2250_, 0, v_inst_2241_);
                leanh::lean_closure_set(v___f_2250_, 1, v_a_2244_);
                v___x_2251_ = leanh::lean_unsigned_to_nat(1);
                v___x_2252_ = lean_nat_sub(v_size_2245_, v___x_2251_);
                leanh::lean_dec(v_size_2245_);
                v___x_2253_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_2242_,
                    v_buckets_2246_,
                    v_a_2244_,
                    v___f_2250_,
                );
                if v_isShared_2249_ == 0 {
                    leanh::lean_ctor_set(v___x_2248_, 1, v___x_2253_);
                    leanh::lean_ctor_set(v___x_2248_, 0, v___x_2252_);
                    v___x_2255_ = v___x_2248_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2256_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2253_);
                    v___x_2255_ = v_reuseFailAlloc_2256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux(
    mut v_00_u03b1_2258_: *mut leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut leanh::LeanObject,
    mut v_inst_2260_: *mut leanh::LeanObject,
    mut v_inst_2261_: *mut leanh::LeanObject,
    mut v_m_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(
        v_inst_2260_,
        v_inst_2261_,
        v_m_2262_,
        v_a_2263_,
    );
    return v___x_2264_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(
    mut v_inst_2265_: *mut leanh::LeanObject,
    mut v_inst_2266_: *mut leanh::LeanObject,
    mut v_m_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2269_: u8 = 0;
    leanh::lean_inc(v_a_2268_);
    leanh::lean_inc_ref(v_inst_2266_);
    leanh::lean_inc_ref(v_inst_2265_);
    v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
        v_inst_2265_,
        v_inst_2266_,
        v_m_2267_,
        v_a_2268_,
    );
    if v___x_2269_ == 0 {
        leanh::lean_dec(v_a_2268_);
        leanh::lean_dec_ref(v_inst_2266_);
        leanh::lean_dec_ref(v_inst_2265_);
        return v_m_2267_;
    } else {
        let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2270_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(
            v_inst_2265_,
            v_inst_2266_,
            v_m_2267_,
            v_a_2268_,
        );
        return v___x_2270_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098(
    mut v_00_u03b1_2271_: *mut leanh::LeanObject,
    mut v_00_u03b2_2272_: *mut leanh::LeanObject,
    mut v_inst_2273_: *mut leanh::LeanObject,
    mut v_inst_2274_: *mut leanh::LeanObject,
    mut v_m_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(
        v_inst_2273_,
        v_inst_2274_,
        v_m_2275_,
        v_a_2276_,
    );
    return v___x_2277_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0(
    mut v_inst_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_f_2280_: *mut leanh::LeanObject,
    mut v_l_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
        v_inst_2278_,
        v_a_2279_,
        v_f_2280_,
        v_l_2281_,
    );
    return v___x_2282_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(
    mut v_inst_2283_: *mut leanh::LeanObject,
    mut v_inst_2284_: *mut leanh::LeanObject,
    mut v_m_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_f_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v_val_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut v_unused_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___f_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2286_);
                leanh::lean_inc_ref(v_inst_2284_);
                leanh::lean_inc_ref(v_inst_2283_);
                v___x_2288_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2283_,
                    v_inst_2284_,
                    v_m_2285_,
                    v_a_2286_,
                );
                if v___x_2288_ == 0 {
                    leanh::lean_dec_ref(v_inst_2283_);
                    v___x_2289_ = leanh::lean_box(0);
                    v___x_2290_ = leanh::lean_apply_1(v_f_2287_, v___x_2289_);
                    if leanh::lean_obj_tag(v___x_2290_) == 0 {
                        leanh::lean_dec(v_a_2286_);
                        leanh::lean_dec_ref(v_inst_2284_);
                        return v_m_2285_;
                    } else {
                        v_val_2291_ = leanh::lean_ctor_get(v___x_2290_, 0);
                        leanh::lean_inc(v_val_2291_);
                        leanh::lean_dec_ref_known(v___x_2290_, 1);
                        leanh::lean_inc_ref(v_inst_2284_);
                        v_val_2292_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                            v_inst_2284_,
                            v_m_2285_,
                            v_a_2286_,
                            v_val_2291_,
                        );
                        v_size_2293_ = leanh::lean_ctor_get(v_val_2292_, 0);
                        leanh::lean_inc(v_size_2293_);
                        v_buckets_2294_ = leanh::lean_ctor_get(v_val_2292_, 1);
                        leanh::lean_inc_ref(v_buckets_2294_);
                        v___x_2295_ = leanh::lean_unsigned_to_nat(4);
                        v___x_2296_ = lean_nat_mul(v_size_2293_, v___x_2295_);
                        v___x_2297_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2298_ = lean_nat_div(v___x_2296_, v___x_2297_);
                        leanh::lean_dec(v___x_2296_);
                        v___x_2299_ = lean_array_get_size(v_buckets_2294_);
                        v___x_2300_ = lean_nat_dec_le(v___x_2298_, v___x_2299_);
                        leanh::lean_dec(v___x_2298_);
                        if v___x_2300_ == 0 {
                            v_isSharedCheck_2308_ =
                                (!leanh::lean_is_exclusive(v_val_2292_)) as u8;
                            if v_isSharedCheck_2308_ == 0 {
                                v_unused_2309_ = leanh::lean_ctor_get(v_val_2292_, 1);
                                leanh::lean_dec(v_unused_2309_);
                                v_unused_2310_ = leanh::lean_ctor_get(v_val_2292_, 0);
                                leanh::lean_dec(v_unused_2310_);
                                v___x_2302_ = v_val_2292_;
                                v_isShared_2303_ = v_isSharedCheck_2308_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_2292_);
                                v___x_2302_ = leanh::lean_box(0);
                                v_isShared_2303_ = v_isSharedCheck_2308_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_buckets_2294_);
                            leanh::lean_dec(v_size_2293_);
                            leanh::lean_dec_ref(v_inst_2284_);
                            return v_val_2292_;
                        }
                    }
                } else {
                    v_size_2311_ = leanh::lean_ctor_get(v_m_2285_, 0);
                    v_buckets_2312_ = leanh::lean_ctor_get(v_m_2285_, 1);
                    v_isSharedCheck_2328_ = (!leanh::lean_is_exclusive(v_m_2285_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2314_ = v_m_2285_;
                        v_isShared_2315_ = v_isSharedCheck_2328_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_buckets_2312_);
                        leanh::lean_inc(v_size_2311_);
                        leanh::lean_dec(v_m_2285_);
                        v___x_2314_ = leanh::lean_box(0);
                        v_isShared_2315_ = v_isSharedCheck_2328_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2304_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2284_,
                    v_buckets_2294_,
                );
                if v_isShared_2303_ == 0 {
                    leanh::lean_ctor_set(v___x_2302_, 1, v_val_2304_);
                    v___x_2306_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_size_2293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_val_2304_);
                    v___x_2306_ = v_reuseFailAlloc_2307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2306_;
            }
            3 => {
                leanh::lean_inc_n(v_a_2286_, 2);
                leanh::lean_inc_ref(v_inst_2283_);
                v___f_2316_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2316_, 0, v_inst_2283_);
                leanh::lean_closure_set(v___f_2316_, 1, v_a_2286_);
                leanh::lean_closure_set(v___f_2316_, 2, v_f_2287_);
                leanh::lean_inc_ref(v_inst_2284_);
                v_buckets_x27_2317_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_2284_,
                    v_buckets_2312_,
                    v_a_2286_,
                    v___f_2316_,
                );
                leanh::lean_inc_ref(v_buckets_x27_2317_);
                v___x_2318_ =
                    l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_2317_);
                v___x_2319_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2283_,
                    v_inst_2284_,
                    v___x_2318_,
                    v_a_2286_,
                );
                leanh::lean_dec_ref(v___x_2318_);
                if v___x_2319_ == 0 {
                    v___x_2320_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2321_ = lean_nat_sub(v_size_2311_, v___x_2320_);
                    leanh::lean_dec(v_size_2311_);
                    if v_isShared_2315_ == 0 {
                        leanh::lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2317_);
                        leanh::lean_ctor_set(v___x_2314_, 0, v___x_2321_);
                        v___x_2323_ = v___x_2314_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_buckets_x27_2317_);
                        v___x_2323_ = v_reuseFailAlloc_2324_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2315_ == 0 {
                        leanh::lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2317_);
                        v___x_2326_ = v___x_2314_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_size_2311_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_buckets_x27_2317_);
                        v___x_2326_ = v_reuseFailAlloc_2327_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2323_;
            }
            5 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter_u2098(
    mut v_00_u03b1_2329_: *mut leanh::LeanObject,
    mut v_00_u03b2_2330_: *mut leanh::LeanObject,
    mut v_inst_2331_: *mut leanh::LeanObject,
    mut v_inst_2332_: *mut leanh::LeanObject,
    mut v_inst_2333_: *mut leanh::LeanObject,
    mut v_m_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
    mut v_f_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(
        v_inst_2331_,
        v_inst_2332_,
        v_m_2334_,
        v_a_2335_,
        v_f_2336_,
    );
    return v___x_2337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0(
    mut v_f_2338_: *mut leanh::LeanObject,
    mut v_x_2339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2339_) == 0 {
                    leanh::lean_dec(v_f_2338_);
                    return v_x_2339_;
                } else {
                    v_val_2340_ = leanh::lean_ctor_get(v_x_2339_, 0);
                    v_isSharedCheck_2348_ = (!leanh::lean_is_exclusive(v_x_2339_)) as u8;
                    if v_isSharedCheck_2348_ == 0 {
                        v___x_2342_ = v_x_2339_;
                        v_isShared_2343_ = v_isSharedCheck_2348_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2340_);
                        leanh::lean_dec(v_x_2339_);
                        v___x_2342_ = leanh::lean_box(0);
                        v_isShared_2343_ = v_isSharedCheck_2348_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2344_ = leanh::lean_apply_1(v_f_2338_, v_val_2340_);
                if v_isShared_2343_ == 0 {
                    leanh::lean_ctor_set(v___x_2342_, 0, v___x_2344_);
                    v___x_2346_ = v___x_2342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
                    v___x_2346_ = v_reuseFailAlloc_2347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(
    mut v_inst_2349_: *mut leanh::LeanObject,
    mut v_inst_2350_: *mut leanh::LeanObject,
    mut v_m_2351_: *mut leanh::LeanObject,
    mut v_a_2352_: *mut leanh::LeanObject,
    mut v_f_2353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2354_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2354_, 0, v_f_2353_);
    v___x_2355_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(
        v_inst_2349_,
        v_inst_2350_,
        v_m_2351_,
        v_a_2352_,
        v___f_2354_,
    );
    return v___x_2355_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_modify_u2098(
    mut v_00_u03b1_2356_: *mut leanh::LeanObject,
    mut v_00_u03b2_2357_: *mut leanh::LeanObject,
    mut v_inst_2358_: *mut leanh::LeanObject,
    mut v_inst_2359_: *mut leanh::LeanObject,
    mut v_inst_2360_: *mut leanh::LeanObject,
    mut v_m_2361_: *mut leanh::LeanObject,
    mut v_a_2362_: *mut leanh::LeanObject,
    mut v_f_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(
        v_inst_2358_,
        v_inst_2359_,
        v_m_2361_,
        v_a_2362_,
        v_f_2363_,
    );
    return v___x_2364_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0(
    mut v_inst_2365_: *mut leanh::LeanObject,
    mut v_a_2366_: *mut leanh::LeanObject,
    mut v_f_2367_: *mut leanh::LeanObject,
    mut v_l_2368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
        v_inst_2365_,
        v_a_2366_,
        v_f_2367_,
        v_l_2368_,
    );
    return v___x_2369_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(
    mut v_inst_2370_: *mut leanh::LeanObject,
    mut v_inst_2371_: *mut leanh::LeanObject,
    mut v_m_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_f_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v_val_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_unused_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___f_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2373_);
                leanh::lean_inc_ref(v_inst_2371_);
                leanh::lean_inc_ref(v_inst_2370_);
                v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2370_,
                    v_inst_2371_,
                    v_m_2372_,
                    v_a_2373_,
                );
                if v___x_2375_ == 0 {
                    leanh::lean_dec_ref(v_inst_2370_);
                    v___x_2376_ = leanh::lean_box(0);
                    v___x_2377_ = leanh::lean_apply_1(v_f_2374_, v___x_2376_);
                    if leanh::lean_obj_tag(v___x_2377_) == 0 {
                        leanh::lean_dec(v_a_2373_);
                        leanh::lean_dec_ref(v_inst_2371_);
                        return v_m_2372_;
                    } else {
                        v_val_2378_ = leanh::lean_ctor_get(v___x_2377_, 0);
                        leanh::lean_inc(v_val_2378_);
                        leanh::lean_dec_ref_known(v___x_2377_, 1);
                        leanh::lean_inc_ref(v_inst_2371_);
                        v_val_2379_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                            v_inst_2371_,
                            v_m_2372_,
                            v_a_2373_,
                            v_val_2378_,
                        );
                        v_size_2380_ = leanh::lean_ctor_get(v_val_2379_, 0);
                        leanh::lean_inc(v_size_2380_);
                        v_buckets_2381_ = leanh::lean_ctor_get(v_val_2379_, 1);
                        leanh::lean_inc_ref(v_buckets_2381_);
                        v___x_2382_ = leanh::lean_unsigned_to_nat(4);
                        v___x_2383_ = lean_nat_mul(v_size_2380_, v___x_2382_);
                        v___x_2384_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2385_ = lean_nat_div(v___x_2383_, v___x_2384_);
                        leanh::lean_dec(v___x_2383_);
                        v___x_2386_ = lean_array_get_size(v_buckets_2381_);
                        v___x_2387_ = lean_nat_dec_le(v___x_2385_, v___x_2386_);
                        leanh::lean_dec(v___x_2385_);
                        if v___x_2387_ == 0 {
                            v_isSharedCheck_2395_ =
                                (!leanh::lean_is_exclusive(v_val_2379_)) as u8;
                            if v_isSharedCheck_2395_ == 0 {
                                v_unused_2396_ = leanh::lean_ctor_get(v_val_2379_, 1);
                                leanh::lean_dec(v_unused_2396_);
                                v_unused_2397_ = leanh::lean_ctor_get(v_val_2379_, 0);
                                leanh::lean_dec(v_unused_2397_);
                                v___x_2389_ = v_val_2379_;
                                v_isShared_2390_ = v_isSharedCheck_2395_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_2379_);
                                v___x_2389_ = leanh::lean_box(0);
                                v_isShared_2390_ = v_isSharedCheck_2395_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_buckets_2381_);
                            leanh::lean_dec(v_size_2380_);
                            leanh::lean_dec_ref(v_inst_2371_);
                            return v_val_2379_;
                        }
                    }
                } else {
                    v_size_2398_ = leanh::lean_ctor_get(v_m_2372_, 0);
                    v_buckets_2399_ = leanh::lean_ctor_get(v_m_2372_, 1);
                    v_isSharedCheck_2415_ = (!leanh::lean_is_exclusive(v_m_2372_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2401_ = v_m_2372_;
                        v_isShared_2402_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_buckets_2399_);
                        leanh::lean_inc(v_size_2398_);
                        leanh::lean_dec(v_m_2372_);
                        v___x_2401_ = leanh::lean_box(0);
                        v_isShared_2402_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2371_,
                    v_buckets_2381_,
                );
                if v_isShared_2390_ == 0 {
                    leanh::lean_ctor_set(v___x_2389_, 1, v_val_2391_);
                    v___x_2393_ = v___x_2389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_size_2380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_val_2391_);
                    v___x_2393_ = v_reuseFailAlloc_2394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2393_;
            }
            3 => {
                leanh::lean_inc_n(v_a_2373_, 2);
                leanh::lean_inc_ref(v_inst_2370_);
                v___f_2403_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2403_, 0, v_inst_2370_);
                leanh::lean_closure_set(v___f_2403_, 1, v_a_2373_);
                leanh::lean_closure_set(v___f_2403_, 2, v_f_2374_);
                leanh::lean_inc_ref(v_inst_2371_);
                v_buckets_x27_2404_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_2371_,
                    v_buckets_2399_,
                    v_a_2373_,
                    v___f_2403_,
                );
                leanh::lean_inc_ref(v_buckets_x27_2404_);
                v___x_2405_ =
                    l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_2404_);
                v___x_2406_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2370_,
                    v_inst_2371_,
                    v___x_2405_,
                    v_a_2373_,
                );
                leanh::lean_dec_ref(v___x_2405_);
                if v___x_2406_ == 0 {
                    v___x_2407_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2408_ = lean_nat_sub(v_size_2398_, v___x_2407_);
                    leanh::lean_dec(v_size_2398_);
                    if v_isShared_2402_ == 0 {
                        leanh::lean_ctor_set(v___x_2401_, 1, v_buckets_x27_2404_);
                        leanh::lean_ctor_set(v___x_2401_, 0, v___x_2408_);
                        v___x_2410_ = v___x_2401_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_buckets_x27_2404_);
                        v___x_2410_ = v_reuseFailAlloc_2411_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2402_ == 0 {
                        leanh::lean_ctor_set(v___x_2401_, 1, v_buckets_x27_2404_);
                        v___x_2413_ = v___x_2401_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_size_2398_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_buckets_x27_2404_);
                        v___x_2413_ = v_reuseFailAlloc_2414_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2410_;
            }
            5 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098(
    mut v_00_u03b1_2416_: *mut leanh::LeanObject,
    mut v_00_u03b2_2417_: *mut leanh::LeanObject,
    mut v_inst_2418_: *mut leanh::LeanObject,
    mut v_inst_2419_: *mut leanh::LeanObject,
    mut v_m_2420_: *mut leanh::LeanObject,
    mut v_a_2421_: *mut leanh::LeanObject,
    mut v_f_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(
        v_inst_2418_,
        v_inst_2419_,
        v_m_2420_,
        v_a_2421_,
        v_f_2422_,
    );
    return v___x_2423_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0(
    mut v_f_2424_: *mut leanh::LeanObject,
    mut v_option_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2429_: u8 = 0;
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_option_2425_) == 0 {
                    leanh::lean_dec(v_f_2424_);
                    return v_option_2425_;
                } else {
                    v_val_2426_ = leanh::lean_ctor_get(v_option_2425_, 0);
                    v_isSharedCheck_2434_ =
                        (!leanh::lean_is_exclusive(v_option_2425_)) as u8;
                    if v_isSharedCheck_2434_ == 0 {
                        v___x_2428_ = v_option_2425_;
                        v_isShared_2429_ = v_isSharedCheck_2434_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2426_);
                        leanh::lean_dec(v_option_2425_);
                        v___x_2428_ = leanh::lean_box(0);
                        v_isShared_2429_ = v_isSharedCheck_2434_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2430_ = leanh::lean_apply_1(v_f_2424_, v_val_2426_);
                if v_isShared_2429_ == 0 {
                    leanh::lean_ctor_set(v___x_2428_, 0, v___x_2430_);
                    v___x_2432_ = v___x_2428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
                    v___x_2432_ = v_reuseFailAlloc_2433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(
    mut v_inst_2435_: *mut leanh::LeanObject,
    mut v_inst_2436_: *mut leanh::LeanObject,
    mut v_m_2437_: *mut leanh::LeanObject,
    mut v_a_2438_: *mut leanh::LeanObject,
    mut v_f_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2440_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2440_, 0, v_f_2439_);
    v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(
        v_inst_2435_,
        v_inst_2436_,
        v_m_2437_,
        v_a_2438_,
        v___f_2440_,
    );
    return v___x_2441_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098(
    mut v_00_u03b1_2442_: *mut leanh::LeanObject,
    mut v_00_u03b2_2443_: *mut leanh::LeanObject,
    mut v_inst_2444_: *mut leanh::LeanObject,
    mut v_inst_2445_: *mut leanh::LeanObject,
    mut v_m_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
    mut v_f_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(
        v_inst_2444_,
        v_inst_2445_,
        v_m_2446_,
        v_a_2447_,
        v_f_2448_,
    );
    return v___x_2449_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(
    mut v_f_2450_: *mut leanh::LeanObject,
    mut v_acc_2451_: *mut leanh::LeanObject,
    mut v_a_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2452_) == 0 {
                    leanh::lean_dec_ref(v_f_2450_);
                    return v_acc_2451_;
                } else {
                    v_key_2453_ = leanh::lean_ctor_get(v_a_2452_, 0);
                    v_value_2454_ = leanh::lean_ctor_get(v_a_2452_, 1);
                    v_tail_2455_ = leanh::lean_ctor_get(v_a_2452_, 2);
                    v_isSharedCheck_2466_ = (!leanh::lean_is_exclusive(v_a_2452_)) as u8;
                    if v_isSharedCheck_2466_ == 0 {
                        v___x_2457_ = v_a_2452_;
                        v_isShared_2458_ = v_isSharedCheck_2466_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2455_);
                        leanh::lean_inc(v_value_2454_);
                        leanh::lean_inc(v_key_2453_);
                        leanh::lean_dec(v_a_2452_);
                        v___x_2457_ = leanh::lean_box(0);
                        v_isShared_2458_ = v_isSharedCheck_2466_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_f_2450_);
                leanh::lean_inc(v_key_2453_);
                v___x_2459_ = leanh::lean_apply_2(v_f_2450_, v_key_2453_, v_value_2454_);
                if leanh::lean_obj_tag(v___x_2459_) == 0 {
                    leanh::lean_del_object(v___x_2457_);
                    leanh::lean_dec(v_key_2453_);
                    v_a_2452_ = v_tail_2455_;
                    state = 0;
                    continue;
                } else {
                    v_val_2461_ = leanh::lean_ctor_get(v___x_2459_, 0);
                    leanh::lean_inc(v_val_2461_);
                    leanh::lean_dec_ref_known(v___x_2459_, 1);
                    if v_isShared_2458_ == 0 {
                        leanh::lean_ctor_set(v___x_2457_, 2, v_acc_2451_);
                        leanh::lean_ctor_set(v___x_2457_, 1, v_val_2461_);
                        v___x_2463_ = v___x_2457_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2465_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_key_2453_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_val_2461_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_acc_2451_);
                        v___x_2463_ = v_reuseFailAlloc_2465_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_acc_2451_ = v___x_2463_;
                v_a_2452_ = v_tail_2455_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0(
    mut v_f_2467_: *mut leanh::LeanObject,
    mut v_l_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = leanh::lean_box(0);
    v___x_2470_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_2467_, v___x_2469_, v_l_2468_);
    return v___x_2470_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(
    mut v_m_2471_: *mut leanh::LeanObject,
    mut v_f_2472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2473_ = leanh::lean_ctor_get(v_m_2471_, 1);
    leanh::lean_inc_ref(v_buckets_2473_);
    leanh::lean_dec_ref(v_m_2471_);
    v___f_2474_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2474_, 0, v_f_2472_);
    v___x_2475_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_2473_, v___f_2474_);
    v___x_2476_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(
    mut v_00_u03b1_2477_: *mut leanh::LeanObject,
    mut v_00_u03b2_2478_: *mut leanh::LeanObject,
    mut v_00_u03b4_2479_: *mut leanh::LeanObject,
    mut v_m_2480_: *mut leanh::LeanObject,
    mut v_f_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(v_m_2480_, v_f_2481_);
    return v___x_2482_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(
    mut v_00_u03b1_2483_: *mut leanh::LeanObject,
    mut v_00_u03b2_2484_: *mut leanh::LeanObject,
    mut v_00_u03b4_2485_: *mut leanh::LeanObject,
    mut v_f_2486_: *mut leanh::LeanObject,
    mut v_acc_2487_: *mut leanh::LeanObject,
    mut v_a_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_2486_, v_acc_2487_, v_a_2488_);
    return v___x_2489_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(
    mut v_f_2490_: *mut leanh::LeanObject,
    mut v_acc_2491_: *mut leanh::LeanObject,
    mut v_a_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2492_) == 0 {
                    leanh::lean_dec(v_f_2490_);
                    return v_acc_2491_;
                } else {
                    v_key_2493_ = leanh::lean_ctor_get(v_a_2492_, 0);
                    v_value_2494_ = leanh::lean_ctor_get(v_a_2492_, 1);
                    v_tail_2495_ = leanh::lean_ctor_get(v_a_2492_, 2);
                    v_isSharedCheck_2504_ = (!leanh::lean_is_exclusive(v_a_2492_)) as u8;
                    if v_isSharedCheck_2504_ == 0 {
                        v___x_2497_ = v_a_2492_;
                        v_isShared_2498_ = v_isSharedCheck_2504_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2495_);
                        leanh::lean_inc(v_value_2494_);
                        leanh::lean_inc(v_key_2493_);
                        leanh::lean_dec(v_a_2492_);
                        v___x_2497_ = leanh::lean_box(0);
                        v_isShared_2498_ = v_isSharedCheck_2504_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_f_2490_);
                leanh::lean_inc(v_key_2493_);
                v___x_2499_ = leanh::lean_apply_2(v_f_2490_, v_key_2493_, v_value_2494_);
                if v_isShared_2498_ == 0 {
                    leanh::lean_ctor_set(v___x_2497_, 2, v_acc_2491_);
                    leanh::lean_ctor_set(v___x_2497_, 1, v___x_2499_);
                    v___x_2501_ = v___x_2497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_key_2493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_acc_2491_);
                    v___x_2501_ = v_reuseFailAlloc_2503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_acc_2491_ = v___x_2501_;
                v_a_2492_ = v_tail_2495_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0(
    mut v_f_2505_: *mut leanh::LeanObject,
    mut v___y_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = leanh::lean_box(0);
    v___x_2508_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_2505_, v___x_2507_, v___y_2506_);
    return v___x_2508_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(
    mut v_m_2509_: *mut leanh::LeanObject,
    mut v_f_2510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___f_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2511_ = leanh::lean_ctor_get(v_m_2509_, 0);
                v_buckets_2512_ = leanh::lean_ctor_get(v_m_2509_, 1);
                v_isSharedCheck_2521_ = (!leanh::lean_is_exclusive(v_m_2509_)) as u8;
                if v_isSharedCheck_2521_ == 0 {
                    v___x_2514_ = v_m_2509_;
                    v_isShared_2515_ = v_isSharedCheck_2521_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2512_);
                    leanh::lean_inc(v_size_2511_);
                    leanh::lean_dec(v_m_2509_);
                    v___x_2514_ = leanh::lean_box(0);
                    v_isShared_2515_ = v_isSharedCheck_2521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2516_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2516_, 0, v_f_2510_);
                v___x_2517_ =
                    l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_2512_, v___f_2516_);
                if v_isShared_2515_ == 0 {
                    leanh::lean_ctor_set(v___x_2514_, 1, v___x_2517_);
                    v___x_2519_ = v___x_2514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_size_2511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2517_);
                    v___x_2519_ = v_reuseFailAlloc_2520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map_u2098(
    mut v_00_u03b1_2522_: *mut leanh::LeanObject,
    mut v_00_u03b2_2523_: *mut leanh::LeanObject,
    mut v_00_u03b4_2524_: *mut leanh::LeanObject,
    mut v_m_2525_: *mut leanh::LeanObject,
    mut v_f_2526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(v_m_2525_, v_f_2526_);
    return v___x_2527_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(
    mut v_00_u03b1_2528_: *mut leanh::LeanObject,
    mut v_00_u03b2_2529_: *mut leanh::LeanObject,
    mut v_00_u03b4_2530_: *mut leanh::LeanObject,
    mut v_f_2531_: *mut leanh::LeanObject,
    mut v_acc_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2534_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_2531_, v_acc_2532_, v_a_2533_);
    return v___x_2534_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(
    mut v_f_2535_: *mut leanh::LeanObject,
    mut v_acc_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2543_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2537_) == 0 {
                    leanh::lean_dec_ref(v_f_2535_);
                    return v_acc_2536_;
                } else {
                    v_key_2538_ = leanh::lean_ctor_get(v_a_2537_, 0);
                    v_value_2539_ = leanh::lean_ctor_get(v_a_2537_, 1);
                    v_tail_2540_ = leanh::lean_ctor_get(v_a_2537_, 2);
                    v_isSharedCheck_2551_ = (!leanh::lean_is_exclusive(v_a_2537_)) as u8;
                    if v_isSharedCheck_2551_ == 0 {
                        v___x_2542_ = v_a_2537_;
                        v_isShared_2543_ = v_isSharedCheck_2551_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2540_);
                        leanh::lean_inc(v_value_2539_);
                        leanh::lean_inc(v_key_2538_);
                        leanh::lean_dec(v_a_2537_);
                        v___x_2542_ = leanh::lean_box(0);
                        v_isShared_2543_ = v_isSharedCheck_2551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_f_2535_);
                leanh::lean_inc(v_value_2539_);
                leanh::lean_inc(v_key_2538_);
                v___x_2544_ = leanh::lean_apply_2(v_f_2535_, v_key_2538_, v_value_2539_);
                v___x_2545_ = (leanh::lean_unbox(v___x_2544_) as u8);
                if v___x_2545_ == 0 {
                    leanh::lean_del_object(v___x_2542_);
                    leanh::lean_dec(v_value_2539_);
                    leanh::lean_dec(v_key_2538_);
                    v_a_2537_ = v_tail_2540_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_2543_ == 0 {
                        leanh::lean_ctor_set(v___x_2542_, 2, v_acc_2536_);
                        v___x_2548_ = v___x_2542_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2550_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_key_2538_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_value_2539_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_acc_2536_);
                        v___x_2548_ = v_reuseFailAlloc_2550_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_acc_2536_ = v___x_2548_;
                v_a_2537_ = v_tail_2540_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0(
    mut v_f_2552_: *mut leanh::LeanObject,
    mut v_l_2553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = leanh::lean_box(0);
    v___x_2555_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_2552_, v___x_2554_, v_l_2553_);
    return v___x_2555_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(
    mut v_m_2556_: *mut leanh::LeanObject,
    mut v_f_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2558_ = leanh::lean_ctor_get(v_m_2556_, 1);
    leanh::lean_inc_ref(v_buckets_2558_);
    leanh::lean_dec_ref(v_m_2556_);
    v___f_2559_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2559_, 0, v_f_2557_);
    v___x_2560_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_2558_, v___f_2559_);
    v___x_2561_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_2560_);
    return v___x_2561_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(
    mut v_00_u03b1_2562_: *mut leanh::LeanObject,
    mut v_00_u03b2_2563_: *mut leanh::LeanObject,
    mut v_m_2564_: *mut leanh::LeanObject,
    mut v_f_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_2564_, v_f_2565_);
    return v___x_2566_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(
    mut v_00_u03b1_2567_: *mut leanh::LeanObject,
    mut v_00_u03b2_2568_: *mut leanh::LeanObject,
    mut v_f_2569_: *mut leanh::LeanObject,
    mut v_acc_2570_: *mut leanh::LeanObject,
    mut v_a_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_2569_, v_acc_2570_, v_a_2571_);
    return v___x_2572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(
    mut v_inst_2573_: *mut leanh::LeanObject,
    mut v_inst_2574_: *mut leanh::LeanObject,
    mut v_m_2575_: *mut leanh::LeanObject,
    mut v_l_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_2576_) == 0 {
                    leanh::lean_dec_ref(v_inst_2574_);
                    leanh::lean_dec_ref(v_inst_2573_);
                    return v_m_2575_;
                } else {
                    v_head_2577_ = leanh::lean_ctor_get(v_l_2576_, 0);
                    leanh::lean_inc(v_head_2577_);
                    v_tail_2578_ = leanh::lean_ctor_get(v_l_2576_, 1);
                    leanh::lean_inc(v_tail_2578_);
                    leanh::lean_dec_ref_known(v_l_2576_, 2);
                    v_fst_2579_ = leanh::lean_ctor_get(v_head_2577_, 0);
                    leanh::lean_inc(v_fst_2579_);
                    v_snd_2580_ = leanh::lean_ctor_get(v_head_2577_, 1);
                    leanh::lean_inc(v_snd_2580_);
                    leanh::lean_dec(v_head_2577_);
                    leanh::lean_inc_ref(v_inst_2574_);
                    leanh::lean_inc_ref(v_inst_2573_);
                    v___x_2581_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_inst_2573_,
                        v_inst_2574_,
                        v_m_2575_,
                        v_fst_2579_,
                        v_snd_2580_,
                    );
                    v_m_2575_ = v___x_2581_;
                    v_l_2576_ = v_tail_2578_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098(
    mut v_00_u03b1_2583_: *mut leanh::LeanObject,
    mut v_00_u03b2_2584_: *mut leanh::LeanObject,
    mut v_inst_2585_: *mut leanh::LeanObject,
    mut v_inst_2586_: *mut leanh::LeanObject,
    mut v_m_2587_: *mut leanh::LeanObject,
    mut v_l_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(
        v_inst_2585_,
        v_inst_2586_,
        v_m_2587_,
        v_l_2588_,
    );
    return v___x_2589_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(
    mut v_inst_2590_: *mut leanh::LeanObject,
    mut v_inst_2591_: *mut leanh::LeanObject,
    mut v_m_2592_: *mut leanh::LeanObject,
    mut v_l_2593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_2593_) == 0 {
                    leanh::lean_dec_ref(v_inst_2591_);
                    leanh::lean_dec_ref(v_inst_2590_);
                    return v_m_2592_;
                } else {
                    v_head_2594_ = leanh::lean_ctor_get(v_l_2593_, 0);
                    leanh::lean_inc(v_head_2594_);
                    v_tail_2595_ = leanh::lean_ctor_get(v_l_2593_, 1);
                    leanh::lean_inc(v_tail_2595_);
                    leanh::lean_dec_ref_known(v_l_2593_, 2);
                    leanh::lean_inc_ref(v_inst_2591_);
                    leanh::lean_inc_ref(v_inst_2590_);
                    v___x_2596_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
                        v_inst_2590_,
                        v_inst_2591_,
                        v_m_2592_,
                        v_head_2594_,
                    );
                    v_m_2592_ = v___x_2596_;
                    v_l_2593_ = v_tail_2595_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098(
    mut v_00_u03b1_2598_: *mut leanh::LeanObject,
    mut v_00_u03b2_2599_: *mut leanh::LeanObject,
    mut v_inst_2600_: *mut leanh::LeanObject,
    mut v_inst_2601_: *mut leanh::LeanObject,
    mut v_m_2602_: *mut leanh::LeanObject,
    mut v_l_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(
        v_inst_2600_,
        v_inst_2601_,
        v_m_2602_,
        v_l_2603_,
    );
    return v___x_2604_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(
    mut v_inst_2605_: *mut leanh::LeanObject,
    mut v_inst_2606_: *mut leanh::LeanObject,
    mut v_m_u2082_2607_: *mut leanh::LeanObject,
    mut v___x_2608_: u8,
    mut v_k_2609_: *mut leanh::LeanObject,
    mut v_x_2610_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2611_: u8 = 0;
    v___x_2611_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
        v_inst_2605_,
        v_inst_2606_,
        v_m_u2082_2607_,
        v_k_2609_,
    );
    if v___x_2611_ == 0 {
        return v___x_2608_;
    } else {
        let mut v___x_2612_: u8 = 0;
        v___x_2612_ = 0;
        return v___x_2612_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(
    mut v_inst_2613_: *mut leanh::LeanObject,
    mut v_inst_2614_: *mut leanh::LeanObject,
    mut v_m_u2082_2615_: *mut leanh::LeanObject,
    mut v___x_2616_: *mut leanh::LeanObject,
    mut v_k_2617_: *mut leanh::LeanObject,
    mut v_x_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_52__boxed_2619_: u8 = 0;
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_52__boxed_2619_ = (leanh::lean_unbox(v___x_2616_) as u8);
    v_res_2620_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(
        v_inst_2613_,
        v_inst_2614_,
        v_m_u2082_2615_,
        v___x_52__boxed_2619_,
        v_k_2617_,
        v_x_2618_,
    );
    leanh::lean_dec(v_x_2618_);
    leanh::lean_dec_ref(v_m_u2082_2615_);
    v_r_2621_ = leanh::lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(
    mut v_inst_2645_: *mut leanh::LeanObject,
    mut v_inst_2646_: *mut leanh::LeanObject,
    mut v_m_u2081_2647_: *mut leanh::LeanObject,
    mut v_m_u2082_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    v_size_2649_ = leanh::lean_ctor_get(v_m_u2081_2647_, 0);
    v_size_2650_ = leanh::lean_ctor_get(v_m_u2082_2648_, 0);
    v_buckets_2651_ = leanh::lean_ctor_get(v_m_u2082_2648_, 1);
    v___x_2652_ = lean_nat_dec_le(v_size_2649_, v_size_2650_);
    if v___x_2652_ == 0 {
        let mut v___f_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_2651_);
        leanh::lean_dec_ref(v_m_u2082_2648_);
        v___f_2653_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11;
        v___x_2654_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_2651_);
        v___x_2655_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_2653_,
            v_inst_2645_,
            v_inst_2646_,
            v_m_u2081_2647_,
            v___x_2654_,
        );
        return v___x_2655_;
    } else {
        let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2656_ = leanh::lean_box((v___x_2652_) as usize);
        v___f_2657_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_2657_, 0, v_inst_2645_);
        leanh::lean_closure_set(v___f_2657_, 1, v_inst_2646_);
        leanh::lean_closure_set(v___f_2657_, 2, v_m_u2082_2648_);
        leanh::lean_closure_set(v___f_2657_, 3, v___x_2656_);
        v___x_2658_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_u2081_2647_, v___f_2657_);
        return v___x_2658_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(
    mut v_00_u03b1_2659_: *mut leanh::LeanObject,
    mut v_00_u03b2_2660_: *mut leanh::LeanObject,
    mut v_inst_2661_: *mut leanh::LeanObject,
    mut v_inst_2662_: *mut leanh::LeanObject,
    mut v_m_u2081_2663_: *mut leanh::LeanObject,
    mut v_m_u2082_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(
        v_inst_2661_,
        v_inst_2662_,
        v_m_u2081_2663_,
        v_m_u2082_2664_,
    );
    return v___x_2665_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(
    mut v_inst_2666_: *mut leanh::LeanObject,
    mut v_inst_2667_: *mut leanh::LeanObject,
    mut v_m_2668_: *mut leanh::LeanObject,
    mut v_l_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_2669_) == 0 {
                    leanh::lean_dec_ref(v_inst_2667_);
                    leanh::lean_dec_ref(v_inst_2666_);
                    return v_m_2668_;
                } else {
                    v_head_2670_ = leanh::lean_ctor_get(v_l_2669_, 0);
                    leanh::lean_inc(v_head_2670_);
                    v_tail_2671_ = leanh::lean_ctor_get(v_l_2669_, 1);
                    leanh::lean_inc(v_tail_2671_);
                    leanh::lean_dec_ref_known(v_l_2669_, 2);
                    v_fst_2672_ = leanh::lean_ctor_get(v_head_2670_, 0);
                    leanh::lean_inc(v_fst_2672_);
                    v_snd_2673_ = leanh::lean_ctor_get(v_head_2670_, 1);
                    leanh::lean_inc(v_snd_2673_);
                    leanh::lean_dec(v_head_2670_);
                    leanh::lean_inc_ref(v_inst_2667_);
                    leanh::lean_inc_ref(v_inst_2666_);
                    v___x_2674_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                        v_inst_2666_,
                        v_inst_2667_,
                        v_m_2668_,
                        v_fst_2672_,
                        v_snd_2673_,
                    );
                    v_m_2668_ = v___x_2674_;
                    v_l_2669_ = v_tail_2671_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(
    mut v_00_u03b1_2676_: *mut leanh::LeanObject,
    mut v_00_u03b2_2677_: *mut leanh::LeanObject,
    mut v_inst_2678_: *mut leanh::LeanObject,
    mut v_inst_2679_: *mut leanh::LeanObject,
    mut v_m_2680_: *mut leanh::LeanObject,
    mut v_l_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(
        v_inst_2678_,
        v_inst_2679_,
        v_m_2680_,
        v_l_2681_,
    );
    return v___x_2682_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(
    mut v_inst_2683_: *mut leanh::LeanObject,
    mut v_inst_2684_: *mut leanh::LeanObject,
    mut v_m_u2081_2685_: *mut leanh::LeanObject,
    mut v_m_u2082_2686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    v_size_2687_ = leanh::lean_ctor_get(v_m_u2081_2685_, 0);
    v_buckets_2688_ = leanh::lean_ctor_get(v_m_u2081_2685_, 1);
    v_size_2689_ = leanh::lean_ctor_get(v_m_u2082_2686_, 0);
    v_buckets_2690_ = leanh::lean_ctor_get(v_m_u2082_2686_, 1);
    v___x_2691_ = lean_nat_dec_le(v_size_2687_, v_size_2689_);
    if v___x_2691_ == 0 {
        let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_2690_);
        leanh::lean_dec_ref(v_m_u2082_2686_);
        v___x_2692_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_2690_);
        v___x_2693_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(
            v_inst_2683_,
            v_inst_2684_,
            v_m_u2081_2685_,
            v___x_2692_,
        );
        return v___x_2693_;
    } else {
        let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_2688_);
        leanh::lean_dec_ref(v_m_u2081_2685_);
        v___x_2694_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_2688_);
        v___x_2695_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(
            v_inst_2683_,
            v_inst_2684_,
            v_m_u2082_2686_,
            v___x_2694_,
        );
        return v___x_2695_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union_u2098(
    mut v_00_u03b1_2696_: *mut leanh::LeanObject,
    mut v_00_u03b2_2697_: *mut leanh::LeanObject,
    mut v_inst_2698_: *mut leanh::LeanObject,
    mut v_inst_2699_: *mut leanh::LeanObject,
    mut v_m_u2081_2700_: *mut leanh::LeanObject,
    mut v_m_u2082_2701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(
        v_inst_2698_,
        v_inst_2699_,
        v_m_u2081_2700_,
        v_m_u2082_2701_,
    );
    return v___x_2702_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(
    mut v_inst_2703_: *mut leanh::LeanObject,
    mut v_inst_2704_: *mut leanh::LeanObject,
    mut v_m_2705_: *mut leanh::LeanObject,
    mut v_sofar_2706_: *mut leanh::LeanObject,
    mut v_k_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2704_);
    leanh::lean_inc_ref(v_inst_2703_);
    v___x_2708_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
        v_inst_2703_,
        v_inst_2704_,
        v_m_2705_,
        v_k_2707_,
    );
    if leanh::lean_obj_tag(v___x_2708_) == 0 {
        leanh::lean_dec_ref(v_inst_2704_);
        leanh::lean_dec_ref(v_inst_2703_);
        return v_sofar_2706_;
    } else {
        let mut v_val_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2709_ = leanh::lean_ctor_get(v___x_2708_, 0);
        leanh::lean_inc(v_val_2709_);
        leanh::lean_dec_ref_known(v___x_2708_, 1);
        v_fst_2710_ = leanh::lean_ctor_get(v_val_2709_, 0);
        leanh::lean_inc(v_fst_2710_);
        v_snd_2711_ = leanh::lean_ctor_get(v_val_2709_, 1);
        leanh::lean_inc(v_snd_2711_);
        leanh::lean_dec(v_val_2709_);
        v___x_2712_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(
            v_inst_2703_,
            v_inst_2704_,
            v_sofar_2706_,
            v_fst_2710_,
            v_snd_2711_,
        );
        return v___x_2712_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(
    mut v_inst_2713_: *mut leanh::LeanObject,
    mut v_inst_2714_: *mut leanh::LeanObject,
    mut v_m_2715_: *mut leanh::LeanObject,
    mut v_sofar_2716_: *mut leanh::LeanObject,
    mut v_k_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(
        v_inst_2713_,
        v_inst_2714_,
        v_m_2715_,
        v_sofar_2716_,
        v_k_2717_,
    );
    leanh::lean_dec_ref(v_m_2715_);
    return v_res_2718_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(
    mut v_00_u03b1_2719_: *mut leanh::LeanObject,
    mut v_00_u03b2_2720_: *mut leanh::LeanObject,
    mut v_inst_2721_: *mut leanh::LeanObject,
    mut v_inst_2722_: *mut leanh::LeanObject,
    mut v_m_2723_: *mut leanh::LeanObject,
    mut v_sofar_2724_: *mut leanh::LeanObject,
    mut v_k_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(
        v_inst_2721_,
        v_inst_2722_,
        v_m_2723_,
        v_sofar_2724_,
        v_k_2725_,
    );
    return v___x_2726_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(
    mut v_00_u03b1_2727_: *mut leanh::LeanObject,
    mut v_00_u03b2_2728_: *mut leanh::LeanObject,
    mut v_inst_2729_: *mut leanh::LeanObject,
    mut v_inst_2730_: *mut leanh::LeanObject,
    mut v_m_2731_: *mut leanh::LeanObject,
    mut v_sofar_2732_: *mut leanh::LeanObject,
    mut v_k_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(
        v_00_u03b1_2727_,
        v_00_u03b2_2728_,
        v_inst_2729_,
        v_inst_2730_,
        v_m_2731_,
        v_sofar_2732_,
        v_k_2733_,
    );
    leanh::lean_dec_ref(v_m_2731_);
    return v_res_2734_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
    mut v_inst_2735_: *mut leanh::LeanObject,
    mut v_inst_2736_: *mut leanh::LeanObject,
    mut v_m_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2739_ = leanh::lean_ctor_get(v_m_2737_, 1);
    leanh::lean_inc(v_a_2738_);
    v___x_2740_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_2736_, v_buckets_2739_, v_a_2738_);
    v___x_2741_ =
        l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_2735_, v_a_2738_, v___x_2740_);
    return v___x_2741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(
    mut v_inst_2742_: *mut leanh::LeanObject,
    mut v_inst_2743_: *mut leanh::LeanObject,
    mut v_m_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2742_,
        v_inst_2743_,
        v_m_2744_,
        v_a_2745_,
    );
    leanh::lean_dec_ref(v_m_2744_);
    return v_res_2746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(
    mut v_00_u03b1_2747_: *mut leanh::LeanObject,
    mut v_00_u03b2_2748_: *mut leanh::LeanObject,
    mut v_inst_2749_: *mut leanh::LeanObject,
    mut v_inst_2750_: *mut leanh::LeanObject,
    mut v_m_2751_: *mut leanh::LeanObject,
    mut v_a_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2749_,
        v_inst_2750_,
        v_m_2751_,
        v_a_2752_,
    );
    return v___x_2753_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(
    mut v_00_u03b1_2754_: *mut leanh::LeanObject,
    mut v_00_u03b2_2755_: *mut leanh::LeanObject,
    mut v_inst_2756_: *mut leanh::LeanObject,
    mut v_inst_2757_: *mut leanh::LeanObject,
    mut v_m_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(
        v_00_u03b1_2754_,
        v_00_u03b2_2755_,
        v_inst_2756_,
        v_inst_2757_,
        v_m_2758_,
        v_a_2759_,
    );
    leanh::lean_dec_ref(v_m_2758_);
    return v_res_2760_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(
    mut v_inst_2761_: *mut leanh::LeanObject,
    mut v_inst_2762_: *mut leanh::LeanObject,
    mut v_m_2763_: *mut leanh::LeanObject,
    mut v_a_2764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2765_ = leanh::lean_ctor_get(v_m_2763_, 1);
    leanh::lean_inc(v_a_2764_);
    v___x_2766_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_2762_, v_buckets_2765_, v_a_2764_);
    v___x_2767_ =
        l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_2761_, v_a_2764_, v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(
    mut v_inst_2768_: *mut leanh::LeanObject,
    mut v_inst_2769_: *mut leanh::LeanObject,
    mut v_m_2770_: *mut leanh::LeanObject,
    mut v_a_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(
        v_inst_2768_,
        v_inst_2769_,
        v_m_2770_,
        v_a_2771_,
    );
    leanh::lean_dec_ref(v_m_2770_);
    return v_res_2772_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(
    mut v_00_u03b1_2773_: *mut leanh::LeanObject,
    mut v_00_u03b2_2774_: *mut leanh::LeanObject,
    mut v_inst_2775_: *mut leanh::LeanObject,
    mut v_inst_2776_: *mut leanh::LeanObject,
    mut v_m_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
    mut v_h_2779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(
        v_inst_2775_,
        v_inst_2776_,
        v_m_2777_,
        v_a_2778_,
    );
    return v___x_2780_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(
    mut v_00_u03b1_2781_: *mut leanh::LeanObject,
    mut v_00_u03b2_2782_: *mut leanh::LeanObject,
    mut v_inst_2783_: *mut leanh::LeanObject,
    mut v_inst_2784_: *mut leanh::LeanObject,
    mut v_m_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_h_2787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(
        v_00_u03b1_2781_,
        v_00_u03b2_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_m_2785_,
        v_a_2786_,
        v_h_2787_,
    );
    leanh::lean_dec_ref(v_m_2785_);
    return v_res_2788_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(
    mut v_inst_2789_: *mut leanh::LeanObject,
    mut v_inst_2790_: *mut leanh::LeanObject,
    mut v_m_2791_: *mut leanh::LeanObject,
    mut v_a_2792_: *mut leanh::LeanObject,
    mut v_fallback_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2789_,
        v_inst_2790_,
        v_m_2791_,
        v_a_2792_,
    );
    if leanh::lean_obj_tag(v___x_2794_) == 0 {
        leanh::lean_inc(v_fallback_2793_);
        return v_fallback_2793_;
    } else {
        let mut v_val_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2795_ = leanh::lean_ctor_get(v___x_2794_, 0);
        leanh::lean_inc(v_val_2795_);
        leanh::lean_dec_ref_known(v___x_2794_, 1);
        return v_val_2795_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(
    mut v_inst_2796_: *mut leanh::LeanObject,
    mut v_inst_2797_: *mut leanh::LeanObject,
    mut v_m_2798_: *mut leanh::LeanObject,
    mut v_a_2799_: *mut leanh::LeanObject,
    mut v_fallback_2800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(
        v_inst_2796_,
        v_inst_2797_,
        v_m_2798_,
        v_a_2799_,
        v_fallback_2800_,
    );
    leanh::lean_dec(v_fallback_2800_);
    leanh::lean_dec_ref(v_m_2798_);
    return v_res_2801_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(
    mut v_00_u03b1_2802_: *mut leanh::LeanObject,
    mut v_00_u03b2_2803_: *mut leanh::LeanObject,
    mut v_inst_2804_: *mut leanh::LeanObject,
    mut v_inst_2805_: *mut leanh::LeanObject,
    mut v_m_2806_: *mut leanh::LeanObject,
    mut v_a_2807_: *mut leanh::LeanObject,
    mut v_fallback_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(
        v_inst_2804_,
        v_inst_2805_,
        v_m_2806_,
        v_a_2807_,
        v_fallback_2808_,
    );
    return v___x_2809_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(
    mut v_00_u03b1_2810_: *mut leanh::LeanObject,
    mut v_00_u03b2_2811_: *mut leanh::LeanObject,
    mut v_inst_2812_: *mut leanh::LeanObject,
    mut v_inst_2813_: *mut leanh::LeanObject,
    mut v_m_2814_: *mut leanh::LeanObject,
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_fallback_2816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(
        v_00_u03b1_2810_,
        v_00_u03b2_2811_,
        v_inst_2812_,
        v_inst_2813_,
        v_m_2814_,
        v_a_2815_,
        v_fallback_2816_,
    );
    leanh::lean_dec(v_fallback_2816_);
    leanh::lean_dec_ref(v_m_2814_);
    return v_res_2817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(
    mut v_inst_2818_: *mut leanh::LeanObject,
    mut v_inst_2819_: *mut leanh::LeanObject,
    mut v_inst_2820_: *mut leanh::LeanObject,
    mut v_m_2821_: *mut leanh::LeanObject,
    mut v_a_2822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2818_,
        v_inst_2819_,
        v_m_2821_,
        v_a_2822_,
    );
    if leanh::lean_obj_tag(v___x_2823_) == 0 {
        let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2824_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once
            ),
            _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3,
        );
        v___x_2825_ = l_panic___redArg(v_inst_2820_, v___x_2824_);
        return v___x_2825_;
    } else {
        let mut v_val_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2826_ = leanh::lean_ctor_get(v___x_2823_, 0);
        leanh::lean_inc(v_val_2826_);
        leanh::lean_dec_ref_known(v___x_2823_, 1);
        return v_val_2826_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(
    mut v_inst_2827_: *mut leanh::LeanObject,
    mut v_inst_2828_: *mut leanh::LeanObject,
    mut v_inst_2829_: *mut leanh::LeanObject,
    mut v_m_2830_: *mut leanh::LeanObject,
    mut v_a_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(
        v_inst_2827_,
        v_inst_2828_,
        v_inst_2829_,
        v_m_2830_,
        v_a_2831_,
    );
    leanh::lean_dec_ref(v_m_2830_);
    leanh::lean_dec(v_inst_2829_);
    return v_res_2832_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(
    mut v_00_u03b1_2833_: *mut leanh::LeanObject,
    mut v_00_u03b2_2834_: *mut leanh::LeanObject,
    mut v_inst_2835_: *mut leanh::LeanObject,
    mut v_inst_2836_: *mut leanh::LeanObject,
    mut v_inst_2837_: *mut leanh::LeanObject,
    mut v_m_2838_: *mut leanh::LeanObject,
    mut v_a_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(
        v_inst_2835_,
        v_inst_2836_,
        v_inst_2837_,
        v_m_2838_,
        v_a_2839_,
    );
    return v___x_2840_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(
    mut v_00_u03b1_2841_: *mut leanh::LeanObject,
    mut v_00_u03b2_2842_: *mut leanh::LeanObject,
    mut v_inst_2843_: *mut leanh::LeanObject,
    mut v_inst_2844_: *mut leanh::LeanObject,
    mut v_inst_2845_: *mut leanh::LeanObject,
    mut v_m_2846_: *mut leanh::LeanObject,
    mut v_a_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(
        v_00_u03b1_2841_,
        v_00_u03b2_2842_,
        v_inst_2843_,
        v_inst_2844_,
        v_inst_2845_,
        v_m_2846_,
        v_a_2847_,
    );
    leanh::lean_dec_ref(v_m_2846_);
    leanh::lean_dec(v_inst_2845_);
    return v_res_2848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(
    mut v_inst_2849_: *mut leanh::LeanObject,
    mut v_inst_2850_: *mut leanh::LeanObject,
    mut v_m_2851_: *mut leanh::LeanObject,
    mut v_l_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_2852_) == 0 {
                    leanh::lean_dec_ref(v_inst_2850_);
                    leanh::lean_dec_ref(v_inst_2849_);
                    return v_m_2851_;
                } else {
                    v_head_2853_ = leanh::lean_ctor_get(v_l_2852_, 0);
                    leanh::lean_inc(v_head_2853_);
                    v_tail_2854_ = leanh::lean_ctor_get(v_l_2852_, 1);
                    leanh::lean_inc(v_tail_2854_);
                    leanh::lean_dec_ref_known(v_l_2852_, 2);
                    v_fst_2855_ = leanh::lean_ctor_get(v_head_2853_, 0);
                    leanh::lean_inc(v_fst_2855_);
                    v_snd_2856_ = leanh::lean_ctor_get(v_head_2853_, 1);
                    leanh::lean_inc(v_snd_2856_);
                    leanh::lean_dec(v_head_2853_);
                    leanh::lean_inc_ref(v_inst_2850_);
                    leanh::lean_inc_ref(v_inst_2849_);
                    v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_inst_2849_,
                        v_inst_2850_,
                        v_m_2851_,
                        v_fst_2855_,
                        v_snd_2856_,
                    );
                    v_m_2851_ = v___x_2857_;
                    v_l_2852_ = v_tail_2854_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(
    mut v_00_u03b1_2859_: *mut leanh::LeanObject,
    mut v_00_u03b2_2860_: *mut leanh::LeanObject,
    mut v_inst_2861_: *mut leanh::LeanObject,
    mut v_inst_2862_: *mut leanh::LeanObject,
    mut v_m_2863_: *mut leanh::LeanObject,
    mut v_l_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(
        v_inst_2861_,
        v_inst_2862_,
        v_m_2863_,
        v_l_2864_,
    );
    return v___x_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(
    mut v_inst_2866_: *mut leanh::LeanObject,
    mut v_inst_2867_: *mut leanh::LeanObject,
    mut v_m_2868_: *mut leanh::LeanObject,
    mut v_l_2869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_2869_) == 0 {
                    leanh::lean_dec_ref(v_inst_2867_);
                    leanh::lean_dec_ref(v_inst_2866_);
                    return v_m_2868_;
                } else {
                    v_head_2870_ = leanh::lean_ctor_get(v_l_2869_, 0);
                    leanh::lean_inc(v_head_2870_);
                    v_tail_2871_ = leanh::lean_ctor_get(v_l_2869_, 1);
                    leanh::lean_inc(v_tail_2871_);
                    leanh::lean_dec_ref_known(v_l_2869_, 2);
                    v___x_2872_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_inst_2867_);
                    leanh::lean_inc_ref(v_inst_2866_);
                    v___x_2873_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                        v_inst_2866_,
                        v_inst_2867_,
                        v_m_2868_,
                        v_head_2870_,
                        v___x_2872_,
                    );
                    v_m_2868_ = v___x_2873_;
                    v_l_2869_ = v_tail_2871_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(
    mut v_00_u03b1_2875_: *mut leanh::LeanObject,
    mut v_inst_2876_: *mut leanh::LeanObject,
    mut v_inst_2877_: *mut leanh::LeanObject,
    mut v_m_2878_: *mut leanh::LeanObject,
    mut v_l_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(
        v_inst_2876_,
        v_inst_2877_,
        v_m_2878_,
        v_l_2879_,
    );
    return v___x_2880_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(
    mut v_m_2881_: *mut leanh::LeanObject,
    mut v_h__1_2882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_2883_ = leanh::lean_ctor_get(v_m_2881_, 0);
    leanh::lean_inc(v_size_2883_);
    v_buckets_2884_ = leanh::lean_ctor_get(v_m_2881_, 1);
    leanh::lean_inc_ref(v_buckets_2884_);
    leanh::lean_dec_ref(v_m_2881_);
    v___x_2885_ = leanh::lean_apply_3(
        v_h__1_2882_,
        v_size_2883_,
        v_buckets_2884_,
        leanh::lean_box(0),
    );
    return v___x_2885_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(
    mut v_00_u03b1_2886_: *mut leanh::LeanObject,
    mut v_00_u03b2_2887_: *mut leanh::LeanObject,
    mut v_motive_2888_: *mut leanh::LeanObject,
    mut v_m_2889_: *mut leanh::LeanObject,
    mut v_h__1_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_2891_ = leanh::lean_ctor_get(v_m_2889_, 0);
    leanh::lean_inc(v_size_2891_);
    v_buckets_2892_ = leanh::lean_ctor_get(v_m_2889_, 1);
    leanh::lean_inc_ref(v_buckets_2892_);
    leanh::lean_dec_ref(v_m_2889_);
    v___x_2893_ = leanh::lean_apply_3(
        v_h__1_2890_,
        v_size_2891_,
        v_buckets_2892_,
        leanh::lean_box(0),
    );
    return v___x_2893_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___redArg(
    mut v_x_2894_: *mut leanh::LeanObject,
    mut v_h__1_2895_: *mut leanh::LeanObject,
    mut v_h__2_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2894_) == 0 {
        let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2896_);
        v___x_2897_ = leanh::lean_box(0);
        v___x_2898_ = leanh::lean_apply_1(v_h__1_2895_, v___x_2897_);
        return v___x_2898_;
    } else {
        let mut v_val_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2895_);
        v_val_2899_ = leanh::lean_ctor_get(v_x_2894_, 0);
        leanh::lean_inc(v_val_2899_);
        leanh::lean_dec_ref_known(v_x_2894_, 1);
        v___x_2900_ = leanh::lean_apply_1(v_h__2_2896_, v_val_2899_);
        return v___x_2900_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(
    mut v_00_u03b1_2901_: *mut leanh::LeanObject,
    mut v_00_u03b2_2902_: *mut leanh::LeanObject,
    mut v_a_2903_: *mut leanh::LeanObject,
    mut v_motive_2904_: *mut leanh::LeanObject,
    mut v_x_2905_: *mut leanh::LeanObject,
    mut v_h__1_2906_: *mut leanh::LeanObject,
    mut v_h__2_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2905_) == 0 {
        let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2907_);
        v___x_2908_ = leanh::lean_box(0);
        v___x_2909_ = leanh::lean_apply_1(v_h__1_2906_, v___x_2908_);
        return v___x_2909_;
    } else {
        let mut v_val_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2906_);
        v_val_2910_ = leanh::lean_ctor_get(v_x_2905_, 0);
        leanh::lean_inc(v_val_2910_);
        leanh::lean_dec_ref_known(v_x_2905_, 1);
        v___x_2911_ = leanh::lean_apply_1(v_h__2_2907_, v_val_2910_);
        return v___x_2911_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___boxed(
    mut v_00_u03b1_2912_: *mut leanh::LeanObject,
    mut v_00_u03b2_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
    mut v_motive_2915_: *mut leanh::LeanObject,
    mut v_x_2916_: *mut leanh::LeanObject,
    mut v_h__1_2917_: *mut leanh::LeanObject,
    mut v_h__2_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2919_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(v_00_u03b1_2912_, v_00_u03b2_2913_, v_a_2914_, v_motive_2915_, v_x_2916_, v_h__1_2917_, v_h__2_2918_);
    leanh::lean_dec(v_a_2914_);
    return v_res_2919_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(
    mut v_x_2920_: *mut leanh::LeanObject,
    mut v_h__1_2921_: *mut leanh::LeanObject,
    mut v_h__2_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2920_) == 0 {
        let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2922_);
        v___x_2923_ = leanh::lean_box(0);
        v___x_2924_ = leanh::lean_apply_1(v_h__1_2921_, v___x_2923_);
        return v___x_2924_;
    } else {
        let mut v_val_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2921_);
        v_val_2925_ = leanh::lean_ctor_get(v_x_2920_, 0);
        leanh::lean_inc(v_val_2925_);
        leanh::lean_dec_ref_known(v_x_2920_, 1);
        v___x_2926_ = leanh::lean_apply_1(v_h__2_2922_, v_val_2925_);
        return v___x_2926_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(
    mut v_00_u03b1_2927_: *mut leanh::LeanObject,
    mut v_00_u03b2_2928_: *mut leanh::LeanObject,
    mut v_a_2929_: *mut leanh::LeanObject,
    mut v_motive_2930_: *mut leanh::LeanObject,
    mut v_x_2931_: *mut leanh::LeanObject,
    mut v_h__1_2932_: *mut leanh::LeanObject,
    mut v_h__2_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2931_) == 0 {
        let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2933_);
        v___x_2934_ = leanh::lean_box(0);
        v___x_2935_ = leanh::lean_apply_1(v_h__1_2932_, v___x_2934_);
        return v___x_2935_;
    } else {
        let mut v_val_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2932_);
        v_val_2936_ = leanh::lean_ctor_get(v_x_2931_, 0);
        leanh::lean_inc(v_val_2936_);
        leanh::lean_dec_ref_known(v_x_2931_, 1);
        v___x_2937_ = leanh::lean_apply_1(v_h__2_2933_, v_val_2936_);
        return v___x_2937_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_2938_: *mut leanh::LeanObject,
    mut v_00_u03b2_2939_: *mut leanh::LeanObject,
    mut v_a_2940_: *mut leanh::LeanObject,
    mut v_motive_2941_: *mut leanh::LeanObject,
    mut v_x_2942_: *mut leanh::LeanObject,
    mut v_h__1_2943_: *mut leanh::LeanObject,
    mut v_h__2_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_2938_, v_00_u03b2_2939_, v_a_2940_, v_motive_2941_, v_x_2942_, v_h__1_2943_, v_h__2_2944_);
    leanh::lean_dec(v_a_2940_);
    return v_res_2945_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(
    mut v_x_2946_: usize,
    mut v_h__1_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = leanh::lean_box_usize(v_x_2946_);
    v___x_2949_ = leanh::lean_apply_2(v_h__1_2947_, v___x_2948_, leanh::lean_box(0));
    return v___x_2949_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg___boxed(
    mut v_x_2950_: *mut leanh::LeanObject,
    mut v_h__1_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_14__boxed_2952_: usize = 0;
    let mut v_res_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_14__boxed_2952_ = leanh::lean_unbox_usize(v_x_2950_);
    leanh::lean_dec(v_x_2950_);
    v_res_2953_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(v_x_14__boxed_2952_, v_h__1_2951_);
    return v_res_2953_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(
    mut v_00_u03b1_2954_: *mut leanh::LeanObject,
    mut v_00_u03b2_2955_: *mut leanh::LeanObject,
    mut v_data_2956_: *mut leanh::LeanObject,
    mut v_motive_2957_: *mut leanh::LeanObject,
    mut v_x_2958_: usize,
    mut v_h__1_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = leanh::lean_box_usize(v_x_2958_);
    v___x_2961_ = leanh::lean_apply_2(v_h__1_2959_, v___x_2960_, leanh::lean_box(0));
    return v___x_2961_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___boxed(
    mut v_00_u03b1_2962_: *mut leanh::LeanObject,
    mut v_00_u03b2_2963_: *mut leanh::LeanObject,
    mut v_data_2964_: *mut leanh::LeanObject,
    mut v_motive_2965_: *mut leanh::LeanObject,
    mut v_x_2966_: *mut leanh::LeanObject,
    mut v_h__1_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_2968_: usize = 0;
    let mut v_res_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_2968_ = leanh::lean_unbox_usize(v_x_2966_);
    leanh::lean_dec(v_x_2966_);
    v_res_2969_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(v_00_u03b1_2962_, v_00_u03b2_2963_, v_data_2964_, v_motive_2965_, v_x_21__boxed_2968_, v_h__1_2967_);
    leanh::lean_dec_ref(v_data_2964_);
    return v_res_2969_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter___redArg(
    mut v_m_2970_: *mut leanh::LeanObject,
    mut v_h__1_2971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_2972_ = leanh::lean_ctor_get(v_m_2970_, 0);
    leanh::lean_inc(v_size_2972_);
    v_buckets_2973_ = leanh::lean_ctor_get(v_m_2970_, 1);
    leanh::lean_inc_ref(v_buckets_2973_);
    leanh::lean_dec_ref(v_m_2970_);
    v___x_2974_ = leanh::lean_apply_3(
        v_h__1_2971_,
        v_size_2972_,
        v_buckets_2973_,
        leanh::lean_box(0),
    );
    return v___x_2974_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter(
    mut v_00_u03b1_2975_: *mut leanh::LeanObject,
    mut v_00_u03b2_2976_: *mut leanh::LeanObject,
    mut v_motive_2977_: *mut leanh::LeanObject,
    mut v_m_2978_: *mut leanh::LeanObject,
    mut v_h__1_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_size_2980_ = leanh::lean_ctor_get(v_m_2978_, 0);
    leanh::lean_inc(v_size_2980_);
    v_buckets_2981_ = leanh::lean_ctor_get(v_m_2978_, 1);
    leanh::lean_inc_ref(v_buckets_2981_);
    leanh::lean_dec_ref(v_m_2978_);
    v___x_2982_ = leanh::lean_apply_3(
        v_h__1_2979_,
        v_size_2980_,
        v_buckets_2981_,
        leanh::lean_box(0),
    );
    return v___x_2982_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(
    mut v_x_2983_: *mut leanh::LeanObject,
    mut v_h__1_2984_: *mut leanh::LeanObject,
    mut v_h__2_2985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2983_) == 0 {
        let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2985_);
        v___x_2986_ = leanh::lean_box(0);
        v___x_2987_ = leanh::lean_apply_1(v_h__1_2984_, v___x_2986_);
        return v___x_2987_;
    } else {
        let mut v_val_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2984_);
        v_val_2988_ = leanh::lean_ctor_get(v_x_2983_, 0);
        leanh::lean_inc(v_val_2988_);
        leanh::lean_dec_ref_known(v_x_2983_, 1);
        v___x_2989_ = leanh::lean_apply_1(v_h__2_2985_, v_val_2988_);
        return v___x_2989_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(
    mut v_00_u03b2_2990_: *mut leanh::LeanObject,
    mut v_motive_2991_: *mut leanh::LeanObject,
    mut v_x_2992_: *mut leanh::LeanObject,
    mut v_h__1_2993_: *mut leanh::LeanObject,
    mut v_h__2_2994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2992_) == 0 {
        let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2994_);
        v___x_2995_ = leanh::lean_box(0);
        v___x_2996_ = leanh::lean_apply_1(v_h__1_2993_, v___x_2995_);
        return v___x_2996_;
    } else {
        let mut v_val_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2993_);
        v_val_2997_ = leanh::lean_ctor_get(v_x_2992_, 0);
        leanh::lean_inc(v_val_2997_);
        leanh::lean_dec_ref_known(v_x_2992_, 1);
        v___x_2998_ = leanh::lean_apply_1(v_h__2_2994_, v_val_2997_);
        return v___x_2998_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(
    mut v_x_2999_: *mut leanh::LeanObject,
    mut v_h__1_3000_: *mut leanh::LeanObject,
    mut v_h__2_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2999_) == 0 {
        let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3001_);
        v___x_3002_ = leanh::lean_box(0);
        v___x_3003_ = leanh::lean_apply_1(v_h__1_3000_, v___x_3002_);
        return v___x_3003_;
    } else {
        let mut v_val_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3000_);
        v_val_3004_ = leanh::lean_ctor_get(v_x_2999_, 0);
        leanh::lean_inc(v_val_3004_);
        leanh::lean_dec_ref_known(v_x_2999_, 1);
        v___x_3005_ = leanh::lean_apply_1(v_h__2_3001_, v_val_3004_);
        return v___x_3005_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(
    mut v_00_u03b2_3006_: *mut leanh::LeanObject,
    mut v_motive_3007_: *mut leanh::LeanObject,
    mut v_x_3008_: *mut leanh::LeanObject,
    mut v_h__1_3009_: *mut leanh::LeanObject,
    mut v_h__2_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3008_) == 0 {
        let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3010_);
        v___x_3011_ = leanh::lean_box(0);
        v___x_3012_ = leanh::lean_apply_1(v_h__1_3009_, v___x_3011_);
        return v___x_3012_;
    } else {
        let mut v_val_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3009_);
        v_val_3013_ = leanh::lean_ctor_get(v_x_3008_, 0);
        leanh::lean_inc(v_val_3013_);
        leanh::lean_dec_ref_known(v_x_3008_, 1);
        v___x_3014_ = leanh::lean_apply_1(v_h__2_3010_, v_val_3013_);
        return v___x_3014_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(
    mut v_x_3015_: usize,
    mut v_h__1_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = leanh::lean_box_usize(v_x_3015_);
    v___x_3018_ = leanh::lean_apply_2(v_h__1_3016_, v___x_3017_, leanh::lean_box(0));
    return v___x_3018_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(
    mut v_x_3019_: *mut leanh::LeanObject,
    mut v_h__1_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_14__boxed_3021_: usize = 0;
    let mut v_res_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_14__boxed_3021_ = leanh::lean_unbox_usize(v_x_3019_);
    leanh::lean_dec(v_x_3019_);
    v_res_3022_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(v_x_14__boxed_3021_, v_h__1_3020_);
    return v_res_3022_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(
    mut v_00_u03b1_3023_: *mut leanh::LeanObject,
    mut v_00_u03b2_3024_: *mut leanh::LeanObject,
    mut v_buckets_3025_: *mut leanh::LeanObject,
    mut v_motive_3026_: *mut leanh::LeanObject,
    mut v_x_3027_: usize,
    mut v_h__1_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = leanh::lean_box_usize(v_x_3027_);
    v___x_3030_ = leanh::lean_apply_2(v_h__1_3028_, v___x_3029_, leanh::lean_box(0));
    return v___x_3030_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(
    mut v_00_u03b1_3031_: *mut leanh::LeanObject,
    mut v_00_u03b2_3032_: *mut leanh::LeanObject,
    mut v_buckets_3033_: *mut leanh::LeanObject,
    mut v_motive_3034_: *mut leanh::LeanObject,
    mut v_x_3035_: *mut leanh::LeanObject,
    mut v_h__1_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_3037_: usize = 0;
    let mut v_res_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_3037_ = leanh::lean_unbox_usize(v_x_3035_);
    leanh::lean_dec(v_x_3035_);
    v_res_3038_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(v_00_u03b1_3031_, v_00_u03b2_3032_, v_buckets_3033_, v_motive_3034_, v_x_21__boxed_3037_, v_h__1_3036_);
    leanh::lean_dec_ref(v_buckets_3033_);
    return v_res_3038_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(
    mut v_l_3039_: *mut leanh::LeanObject,
    mut v_h__1_3040_: *mut leanh::LeanObject,
    mut v_h__2_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_3039_) == 0 {
        let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3041_);
        v___x_3042_ = leanh::lean_box(0);
        v___x_3043_ = leanh::lean_apply_1(v_h__1_3040_, v___x_3042_);
        return v___x_3043_;
    } else {
        let mut v_head_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3040_);
        v_head_3044_ = leanh::lean_ctor_get(v_l_3039_, 0);
        leanh::lean_inc(v_head_3044_);
        v_tail_3045_ = leanh::lean_ctor_get(v_l_3039_, 1);
        leanh::lean_inc(v_tail_3045_);
        leanh::lean_dec_ref_known(v_l_3039_, 2);
        v___x_3046_ = leanh::lean_apply_2(v_h__2_3041_, v_head_3044_, v_tail_3045_);
        return v___x_3046_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(
    mut v_00_u03b1_3047_: *mut leanh::LeanObject,
    mut v_00_u03b2_3048_: *mut leanh::LeanObject,
    mut v_motive_3049_: *mut leanh::LeanObject,
    mut v_l_3050_: *mut leanh::LeanObject,
    mut v_h__1_3051_: *mut leanh::LeanObject,
    mut v_h__2_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_3050_) == 0 {
        let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3052_);
        v___x_3053_ = leanh::lean_box(0);
        v___x_3054_ = leanh::lean_apply_1(v_h__1_3051_, v___x_3053_);
        return v___x_3054_;
    } else {
        let mut v_head_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3051_);
        v_head_3055_ = leanh::lean_ctor_get(v_l_3050_, 0);
        leanh::lean_inc(v_head_3055_);
        v_tail_3056_ = leanh::lean_ctor_get(v_l_3050_, 1);
        leanh::lean_inc(v_tail_3056_);
        leanh::lean_dec_ref_known(v_l_3050_, 2);
        v___x_3057_ = leanh::lean_apply_2(v_h__2_3052_, v_head_3055_, v_tail_3056_);
        return v___x_3057_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(
    mut v_l_3058_: *mut leanh::LeanObject,
    mut v_h__1_3059_: *mut leanh::LeanObject,
    mut v_h__2_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_3058_) == 0 {
        let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3060_);
        v___x_3061_ = leanh::lean_box(0);
        v___x_3062_ = leanh::lean_apply_1(v_h__1_3059_, v___x_3061_);
        return v___x_3062_;
    } else {
        let mut v_head_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3059_);
        v_head_3063_ = leanh::lean_ctor_get(v_l_3058_, 0);
        leanh::lean_inc(v_head_3063_);
        v_tail_3064_ = leanh::lean_ctor_get(v_l_3058_, 1);
        leanh::lean_inc(v_tail_3064_);
        leanh::lean_dec_ref_known(v_l_3058_, 2);
        v___x_3065_ = leanh::lean_apply_2(v_h__2_3060_, v_head_3063_, v_tail_3064_);
        return v___x_3065_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(
    mut v_00_u03b1_3066_: *mut leanh::LeanObject,
    mut v_motive_3067_: *mut leanh::LeanObject,
    mut v_l_3068_: *mut leanh::LeanObject,
    mut v_h__1_3069_: *mut leanh::LeanObject,
    mut v_h__2_3070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_3068_) == 0 {
        let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3070_);
        v___x_3071_ = leanh::lean_box(0);
        v___x_3072_ = leanh::lean_apply_1(v_h__1_3069_, v___x_3071_);
        return v___x_3072_;
    } else {
        let mut v_head_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3069_);
        v_head_3073_ = leanh::lean_ctor_get(v_l_3068_, 0);
        leanh::lean_inc(v_head_3073_);
        v_tail_3074_ = leanh::lean_ctor_get(v_l_3068_, 1);
        leanh::lean_inc(v_tail_3074_);
        leanh::lean_dec_ref_known(v_l_3068_, 2);
        v___x_3075_ = leanh::lean_apply_2(v_h__2_3070_, v_head_3073_, v_tail_3074_);
        return v___x_3075_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(
    mut v_l_3076_: *mut leanh::LeanObject,
    mut v_h__1_3077_: *mut leanh::LeanObject,
    mut v_h__2_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_3076_) == 0 {
        let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3078_);
        v___x_3079_ = leanh::lean_box(0);
        v___x_3080_ = leanh::lean_apply_1(v_h__1_3077_, v___x_3079_);
        return v___x_3080_;
    } else {
        let mut v_head_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3077_);
        v_head_3081_ = leanh::lean_ctor_get(v_l_3076_, 0);
        leanh::lean_inc(v_head_3081_);
        v_tail_3082_ = leanh::lean_ctor_get(v_l_3076_, 1);
        leanh::lean_inc(v_tail_3082_);
        leanh::lean_dec_ref_known(v_l_3076_, 2);
        v___x_3083_ = leanh::lean_apply_2(v_h__2_3078_, v_head_3081_, v_tail_3082_);
        return v___x_3083_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(
    mut v_00_u03b1_3084_: *mut leanh::LeanObject,
    mut v_00_u03b2_3085_: *mut leanh::LeanObject,
    mut v_motive_3086_: *mut leanh::LeanObject,
    mut v_l_3087_: *mut leanh::LeanObject,
    mut v_h__1_3088_: *mut leanh::LeanObject,
    mut v_h__2_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_3087_) == 0 {
        let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3089_);
        v___x_3090_ = leanh::lean_box(0);
        v___x_3091_ = leanh::lean_apply_1(v_h__1_3088_, v___x_3090_);
        return v___x_3091_;
    } else {
        let mut v_head_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3088_);
        v_head_3092_ = leanh::lean_ctor_get(v_l_3087_, 0);
        leanh::lean_inc(v_head_3092_);
        v_tail_3093_ = leanh::lean_ctor_get(v_l_3087_, 1);
        leanh::lean_inc(v_tail_3093_);
        leanh::lean_dec_ref_known(v_l_3087_, 2);
        v___x_3094_ = leanh::lean_apply_2(v_h__2_3089_, v_head_3092_, v_tail_3093_);
        return v___x_3094_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_Model(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_Model(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_Model(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_Model(builtin);
}