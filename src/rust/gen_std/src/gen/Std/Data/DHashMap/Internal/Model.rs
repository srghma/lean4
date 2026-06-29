// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Model
// Imports: Init.Data.Array.TakeDrop Std.Data.DHashMap.Basic Std.Data.DHashMap.Internal.Defs Std.Data.DHashMap.Internal.HashesTo Std.Data.DHashMap.Internal.AssocList.Lemmas Init.Data.Array.Bootstrap Init.Data.UInt.Lemmas
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
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
pub static l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_bucket___redArg(
    mut v_inst_1548_: *mut crate::leanh::LeanObject,
    mut v_self_1549_: *mut crate::leanh::LeanObject,
    mut v_k_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = lean_array_get_size(v_self_1549_);
    v___x_1552_ = crate::leanh::lean_apply_1(v_inst_1548_, v_k_1550_);
    v___x_1553_ = 32u64;
    v___x_1554_ = crate::leanh::lean_unbox_uint64(v___x_1552_);
    v___x_1555_ = lean_uint64_shift_right(v___x_1554_, v___x_1553_);
    v___x_1556_ = crate::leanh::lean_unbox_uint64(v___x_1552_);
    crate::leanh::lean_dec_ref(v___x_1552_);
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
    crate::leanh::lean_inc(v___x_1566_);
    return v___x_1566_;
}
pub unsafe fn l_Std_DHashMap_Internal_bucket___redArg___boxed(
    mut v_inst_1567_: *mut crate::leanh::LeanObject,
    mut v_self_1568_: *mut crate::leanh::LeanObject,
    mut v_k_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1567_, v_self_1568_, v_k_1569_);
    crate::leanh::lean_dec_ref(v_self_1568_);
    return v_res_1570_;
}
pub unsafe fn l_Std_DHashMap_Internal_bucket(
    mut v_00_u03b1_1571_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1572_: *mut crate::leanh::LeanObject,
    mut v_inst_1573_: *mut crate::leanh::LeanObject,
    mut v_self_1574_: *mut crate::leanh::LeanObject,
    mut v_h_1575_: *mut crate::leanh::LeanObject,
    mut v_k_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1573_, v_self_1574_, v_k_1576_);
    return v___x_1577_;
}
pub unsafe fn l_Std_DHashMap_Internal_bucket___boxed(
    mut v_00_u03b1_1578_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1579_: *mut crate::leanh::LeanObject,
    mut v_inst_1580_: *mut crate::leanh::LeanObject,
    mut v_self_1581_: *mut crate::leanh::LeanObject,
    mut v_h_1582_: *mut crate::leanh::LeanObject,
    mut v_k_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Std_DHashMap_Internal_bucket(
        v_00_u03b1_1578_,
        v_00_u03b2_1579_,
        v_inst_1580_,
        v_self_1581_,
        v_h_1582_,
        v_k_1583_,
    );
    crate::leanh::lean_dec_ref(v_self_1581_);
    return v_res_1584_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateBucket___redArg(
    mut v_inst_1585_: *mut crate::leanh::LeanObject,
    mut v_self_1586_: *mut crate::leanh::LeanObject,
    mut v_k_1587_: *mut crate::leanh::LeanObject,
    mut v_f_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = lean_array_get_size(v_self_1586_);
    v___x_1590_ = crate::leanh::lean_apply_1(v_inst_1585_, v_k_1587_);
    v___x_1591_ = 32u64;
    v___x_1592_ = crate::leanh::lean_unbox_uint64(v___x_1590_);
    v___x_1593_ = lean_uint64_shift_right(v___x_1592_, v___x_1591_);
    v___x_1594_ = crate::leanh::lean_unbox_uint64(v___x_1590_);
    crate::leanh::lean_dec_ref(v___x_1590_);
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
    crate::leanh::lean_inc(v___x_1604_);
    v___x_1605_ = crate::leanh::lean_apply_1(v_f_1588_, v___x_1604_);
    v___x_1606_ = lean_array_uset(v_self_1586_, v___x_1603_, v___x_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateBucket(
    mut v_00_u03b1_1607_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1608_: *mut crate::leanh::LeanObject,
    mut v_inst_1609_: *mut crate::leanh::LeanObject,
    mut v_self_1610_: *mut crate::leanh::LeanObject,
    mut v_h_1611_: *mut crate::leanh::LeanObject,
    mut v_k_1612_: *mut crate::leanh::LeanObject,
    mut v_f_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Std_DHashMap_Internal_updateBucket___redArg(
        v_inst_1609_,
        v_self_1610_,
        v_k_1612_,
        v_f_1613_,
    );
    return v___x_1614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(
    mut v_f_1615_: *mut crate::leanh::LeanObject,
    mut v_sz_1616_: usize,
    mut v_i_1617_: usize,
    mut v_bs_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1619_: u8 = 0;
    let mut v_v_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: usize = 0;
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1619_ = lean_usize_dec_lt(v_i_1617_, v_sz_1616_);
                if v___x_1619_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_1615_);
                    return v_bs_1618_;
                } else {
                    v_v_1620_ = lean_array_uget(v_bs_1618_, v_i_1617_);
                    v___x_1621_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1622_ = lean_array_uset(v_bs_1618_, v_i_1617_, v___x_1621_);
                    crate::leanh::lean_inc_ref(v_f_1615_);
                    v___x_1623_ = crate::leanh::lean_apply_1(v_f_1615_, v_v_1620_);
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
    mut v_f_1628_: *mut crate::leanh::LeanObject,
    mut v_sz_1629_: *mut crate::leanh::LeanObject,
    mut v_i_1630_: *mut crate::leanh::LeanObject,
    mut v_bs_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1632_: usize = 0;
    let mut v_i_boxed_1633_: usize = 0;
    let mut v_res_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1632_ = crate::leanh::lean_unbox_usize(v_sz_1629_);
    crate::leanh::lean_dec(v_sz_1629_);
    v_i_boxed_1633_ = crate::leanh::lean_unbox_usize(v_i_1630_);
    crate::leanh::lean_dec(v_i_1630_);
    v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_1628_, v_sz_boxed_1632_, v_i_boxed_1633_, v_bs_1631_);
    return v_res_1634_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateAllBuckets___redArg(
    mut v_self_1635_: *mut crate::leanh::LeanObject,
    mut v_f_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1637_: usize = 0;
    let mut v___x_1638_: usize = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1637_ = lean_array_size(v_self_1635_);
    v___x_1638_ = 0usize;
    v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_1636_, v_sz_1637_, v___x_1638_, v_self_1635_);
    return v___x_1639_;
}
pub unsafe fn l_Std_DHashMap_Internal_updateAllBuckets(
    mut v_00_u03b1_1640_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1642_: *mut crate::leanh::LeanObject,
    mut v_self_1643_: *mut crate::leanh::LeanObject,
    mut v_f_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_self_1643_, v_f_1644_);
    return v___x_1645_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(
    mut v_00_u03b1_1646_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1647_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1648_: *mut crate::leanh::LeanObject,
    mut v_f_1649_: *mut crate::leanh::LeanObject,
    mut v_sz_1650_: usize,
    mut v_i_1651_: usize,
    mut v_bs_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_1649_, v_sz_1650_, v_i_1651_, v_bs_1652_);
    return v___x_1653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___boxed(
    mut v_00_u03b1_1654_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1655_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1656_: *mut crate::leanh::LeanObject,
    mut v_f_1657_: *mut crate::leanh::LeanObject,
    mut v_sz_1658_: *mut crate::leanh::LeanObject,
    mut v_i_1659_: *mut crate::leanh::LeanObject,
    mut v_bs_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1661_: usize = 0;
    let mut v_i_boxed_1662_: usize = 0;
    let mut v_res_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1661_ = crate::leanh::lean_unbox_usize(v_sz_1658_);
    crate::leanh::lean_dec(v_sz_1658_);
    v_i_boxed_1662_ = crate::leanh::lean_unbox_usize(v_i_1659_);
    crate::leanh::lean_dec(v_i_1659_);
    v_res_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(v_00_u03b1_1654_, v_00_u03b2_1655_, v_00_u03b4_1656_, v_f_1657_, v_sz_boxed_1661_, v_i_boxed_1662_, v_bs_1660_);
    return v_res_1663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(
    mut v_as_1664_: *mut crate::leanh::LeanObject,
    mut v_i_1665_: usize,
    mut v_stop_1666_: usize,
    mut v_b_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v___x_1670_);
                    crate::leanh::lean_dec(v_b_1667_);
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
    mut v_as_1675_: *mut crate::leanh::LeanObject,
    mut v_i_1676_: *mut crate::leanh::LeanObject,
    mut v_stop_1677_: *mut crate::leanh::LeanObject,
    mut v_b_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1679_: usize = 0;
    let mut v_stop_boxed_1680_: usize = 0;
    let mut v_res_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1679_ = crate::leanh::lean_unbox_usize(v_i_1676_);
    crate::leanh::lean_dec(v_i_1676_);
    v_stop_boxed_1680_ = crate::leanh::lean_unbox_usize(v_stop_1677_);
    crate::leanh::lean_dec(v_stop_1677_);
    v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_1675_, v_i_boxed_1679_, v_stop_boxed_1680_, v_b_1678_);
    crate::leanh::lean_dec_ref(v_as_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Std_DHashMap_Internal_withComputedSize___redArg(
    mut v_self_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v___x_1683_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1684_ = lean_array_get_size(v_self_1682_);
    v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
    if v___x_1685_ == 0 {
        let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1686_, 0, v___x_1683_);
        crate::leanh::lean_ctor_set(v___x_1686_, 1, v_self_1682_);
        return v___x_1686_;
    } else {
        let mut v___x_1687_: u8 = 0;
        v___x_1687_ = lean_nat_dec_le(v___x_1684_, v___x_1684_);
        if v___x_1687_ == 0 {
            if v___x_1685_ == 0 {
                let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1688_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1683_);
                crate::leanh::lean_ctor_set(v___x_1688_, 1, v_self_1682_);
                return v___x_1688_;
            } else {
                let mut v___x_1689_: usize = 0;
                let mut v___x_1690_: usize = 0;
                let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1689_ = 0usize;
                v___x_1690_ = lean_usize_of_nat(v___x_1684_);
                v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_1682_, v___x_1689_, v___x_1690_, v___x_1683_);
                v___x_1692_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                crate::leanh::lean_ctor_set(v___x_1692_, 1, v_self_1682_);
                return v___x_1692_;
            }
        } else {
            let mut v___x_1693_: usize = 0;
            let mut v___x_1694_: usize = 0;
            let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1693_ = 0usize;
            v___x_1694_ = lean_usize_of_nat(v___x_1684_);
            v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_1682_, v___x_1693_, v___x_1694_, v___x_1683_);
            v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
            crate::leanh::lean_ctor_set(v___x_1696_, 1, v_self_1682_);
            return v___x_1696_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_withComputedSize(
    mut v_00_u03b1_1697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1698_: *mut crate::leanh::LeanObject,
    mut v_self_1699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_self_1699_);
    return v___x_1700_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(
    mut v_00_u03b1_1701_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1702_: *mut crate::leanh::LeanObject,
    mut v_as_1703_: *mut crate::leanh::LeanObject,
    mut v_i_1704_: usize,
    mut v_stop_1705_: usize,
    mut v_b_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_1703_, v_i_1704_, v_stop_1705_, v_b_1706_);
    return v___x_1707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___boxed(
    mut v_00_u03b1_1708_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1709_: *mut crate::leanh::LeanObject,
    mut v_as_1710_: *mut crate::leanh::LeanObject,
    mut v_i_1711_: *mut crate::leanh::LeanObject,
    mut v_stop_1712_: *mut crate::leanh::LeanObject,
    mut v_b_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1714_: usize = 0;
    let mut v_stop_boxed_1715_: usize = 0;
    let mut v_res_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1714_ = crate::leanh::lean_unbox_usize(v_i_1711_);
    crate::leanh::lean_dec(v_i_1711_);
    v_stop_boxed_1715_ = crate::leanh::lean_unbox_usize(v_stop_1712_);
    crate::leanh::lean_dec(v_stop_1712_);
    v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(v_00_u03b1_1708_, v_00_u03b2_1709_, v_as_1710_, v_i_boxed_1714_, v_stop_boxed_1715_, v_b_1713_);
    crate::leanh::lean_dec_ref(v_as_1710_);
    return v_res_1716_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0(
    mut v_inst_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_b_1719_: *mut crate::leanh::LeanObject,
    mut v_l_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
        v_inst_1717_,
        v_a_1718_,
        v_b_1719_,
        v_l_1720_,
    );
    return v___x_1721_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
    mut v_inst_1723_: *mut crate::leanh::LeanObject,
    mut v_m_1724_: *mut crate::leanh::LeanObject,
    mut v_a_1725_: *mut crate::leanh::LeanObject,
    mut v_b_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___f_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1727_ = crate::leanh::lean_ctor_get(v_m_1724_, 0);
                v_buckets_1728_ = crate::leanh::lean_ctor_get(v_m_1724_, 1);
                v_isSharedCheck_1737_ = (!crate::leanh::lean_is_exclusive(v_m_1724_)) as u8;
                if v_isSharedCheck_1737_ == 0 {
                    v___x_1730_ = v_m_1724_;
                    v_isShared_1731_ = v_isSharedCheck_1737_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1728_);
                    crate::leanh::lean_inc(v_size_1727_);
                    crate::leanh::lean_dec(v_m_1724_);
                    v___x_1730_ = crate::leanh::lean_box(0);
                    v_isShared_1731_ = v_isSharedCheck_1737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1725_);
                v___f_1732_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_1732_, 0, v_inst_1722_);
                crate::leanh::lean_closure_set(v___f_1732_, 1, v_a_1725_);
                crate::leanh::lean_closure_set(v___f_1732_, 2, v_b_1726_);
                v___x_1733_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_1723_,
                    v_buckets_1728_,
                    v_a_1725_,
                    v___f_1732_,
                );
                if v_isShared_1731_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1730_, 1, v___x_1733_);
                    v___x_1735_ = v___x_1730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_size_1727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1733_);
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
    mut v_00_u03b1_1738_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1739_: *mut crate::leanh::LeanObject,
    mut v_inst_1740_: *mut crate::leanh::LeanObject,
    mut v_inst_1741_: *mut crate::leanh::LeanObject,
    mut v_m_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
    mut v_b_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1746_: *mut crate::leanh::LeanObject,
    mut v_b_1747_: *mut crate::leanh::LeanObject,
    mut v_l_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1749_, 0, v_a_1746_);
    crate::leanh::lean_ctor_set(v___x_1749_, 1, v_b_1747_);
    crate::leanh::lean_ctor_set(v___x_1749_, 2, v_l_1748_);
    return v___x_1749_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
    mut v_inst_1750_: *mut crate::leanh::LeanObject,
    mut v_m_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_b_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___f_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1754_ = crate::leanh::lean_ctor_get(v_m_1751_, 0);
                v_buckets_1755_ = crate::leanh::lean_ctor_get(v_m_1751_, 1);
                v_isSharedCheck_1766_ = (!crate::leanh::lean_is_exclusive(v_m_1751_)) as u8;
                if v_isSharedCheck_1766_ == 0 {
                    v___x_1757_ = v_m_1751_;
                    v_isShared_1758_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1755_);
                    crate::leanh::lean_inc(v_size_1754_);
                    crate::leanh::lean_dec(v_m_1751_);
                    v___x_1757_ = crate::leanh::lean_box(0);
                    v_isShared_1758_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1752_);
                v___f_1759_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1759_, 0, v_a_1752_);
                crate::leanh::lean_closure_set(v___f_1759_, 1, v_b_1753_);
                v___x_1760_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1761_ = lean_nat_add(v_size_1754_, v___x_1760_);
                crate::leanh::lean_dec(v_size_1754_);
                v___x_1762_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_1750_,
                    v_buckets_1755_,
                    v_a_1752_,
                    v___f_1759_,
                );
                if v_isShared_1758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1757_, 1, v___x_1762_);
                    crate::leanh::lean_ctor_set(v___x_1757_, 0, v___x_1761_);
                    v___x_1764_ = v___x_1757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
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
    mut v_00_u03b1_1767_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1768_: *mut crate::leanh::LeanObject,
    mut v_inst_1769_: *mut crate::leanh::LeanObject,
    mut v_inst_1770_: *mut crate::leanh::LeanObject,
    mut v_m_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_b_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
        v_inst_1770_,
        v_m_1771_,
        v_a_1772_,
        v_b_1773_,
    );
    return v___x_1774_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___boxed(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1776_: *mut crate::leanh::LeanObject,
    mut v_inst_1777_: *mut crate::leanh::LeanObject,
    mut v_inst_1778_: *mut crate::leanh::LeanObject,
    mut v_m_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_b_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(
        v_00_u03b1_1775_,
        v_00_u03b2_1776_,
        v_inst_1777_,
        v_inst_1778_,
        v_m_1779_,
        v_a_1780_,
        v_b_1781_,
    );
    crate::leanh::lean_dec_ref(v_inst_1777_);
    return v_res_1782_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_inst_1784_: *mut crate::leanh::LeanObject,
    mut v_m_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1787_ = crate::leanh::lean_ctor_get(v_m_1785_, 1);
    crate::leanh::lean_inc(v_a_1786_);
    v___x_1788_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1784_, v_buckets_1787_, v_a_1786_);
    v___x_1789_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
        v_inst_1783_,
        v_a_1786_,
        v___x_1788_,
    );
    return v___x_1789_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_inst_1791_: *mut crate::leanh::LeanObject,
    mut v_m_1792_: *mut crate::leanh::LeanObject,
    mut v_a_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_1790_,
        v_inst_1791_,
        v_m_1792_,
        v_a_1793_,
    );
    crate::leanh::lean_dec_ref(v_m_1792_);
    return v_res_1794_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(
    mut v_00_u03b1_1795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1796_: *mut crate::leanh::LeanObject,
    mut v_inst_1797_: *mut crate::leanh::LeanObject,
    mut v_inst_1798_: *mut crate::leanh::LeanObject,
    mut v_inst_1799_: *mut crate::leanh::LeanObject,
    mut v_m_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_1797_,
        v_inst_1799_,
        v_m_1800_,
        v_a_1801_,
    );
    return v___x_1802_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(
    mut v_00_u03b1_1803_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1804_: *mut crate::leanh::LeanObject,
    mut v_inst_1805_: *mut crate::leanh::LeanObject,
    mut v_inst_1806_: *mut crate::leanh::LeanObject,
    mut v_inst_1807_: *mut crate::leanh::LeanObject,
    mut v_m_1808_: *mut crate::leanh::LeanObject,
    mut v_a_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(
        v_00_u03b1_1803_,
        v_00_u03b2_1804_,
        v_inst_1805_,
        v_inst_1806_,
        v_inst_1807_,
        v_m_1808_,
        v_a_1809_,
    );
    crate::leanh::lean_dec_ref(v_m_1808_);
    return v_res_1810_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
    mut v_inst_1811_: *mut crate::leanh::LeanObject,
    mut v_inst_1812_: *mut crate::leanh::LeanObject,
    mut v_m_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1815_ = crate::leanh::lean_ctor_get(v_m_1813_, 1);
    crate::leanh::lean_inc(v_a_1814_);
    v___x_1816_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1812_, v_buckets_1815_, v_a_1814_);
    v___x_1817_ =
        l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_1811_, v_a_1814_, v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(
    mut v_inst_1818_: *mut crate::leanh::LeanObject,
    mut v_inst_1819_: *mut crate::leanh::LeanObject,
    mut v_m_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_1818_,
        v_inst_1819_,
        v_m_1820_,
        v_a_1821_,
    );
    crate::leanh::lean_dec_ref(v_m_1820_);
    return v_res_1822_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(
    mut v_00_u03b1_1823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1824_: *mut crate::leanh::LeanObject,
    mut v_inst_1825_: *mut crate::leanh::LeanObject,
    mut v_inst_1826_: *mut crate::leanh::LeanObject,
    mut v_m_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_1825_,
        v_inst_1826_,
        v_m_1827_,
        v_a_1828_,
    );
    return v___x_1829_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(
    mut v_00_u03b1_1830_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1831_: *mut crate::leanh::LeanObject,
    mut v_inst_1832_: *mut crate::leanh::LeanObject,
    mut v_inst_1833_: *mut crate::leanh::LeanObject,
    mut v_m_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1836_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(
        v_00_u03b1_1830_,
        v_00_u03b2_1831_,
        v_inst_1832_,
        v_inst_1833_,
        v_m_1834_,
        v_a_1835_,
    );
    crate::leanh::lean_dec_ref(v_m_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
    mut v_inst_1837_: *mut crate::leanh::LeanObject,
    mut v_inst_1838_: *mut crate::leanh::LeanObject,
    mut v_m_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    v_buckets_1841_ = crate::leanh::lean_ctor_get(v_m_1839_, 1);
    crate::leanh::lean_inc(v_a_1840_);
    v___x_1842_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1838_, v_buckets_1841_, v_a_1840_);
    v___x_1843_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1837_, v_a_1840_, v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(
    mut v_inst_1844_: *mut crate::leanh::LeanObject,
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_m_1846_: *mut crate::leanh::LeanObject,
    mut v_a_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1848_: u8 = 0;
    let mut v_r_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
        v_inst_1844_,
        v_inst_1845_,
        v_m_1846_,
        v_a_1847_,
    );
    crate::leanh::lean_dec_ref(v_m_1846_);
    v_r_1849_ = crate::leanh::lean_box((v_res_1848_) as usize);
    return v_r_1849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(
    mut v_00_u03b1_1850_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1851_: *mut crate::leanh::LeanObject,
    mut v_inst_1852_: *mut crate::leanh::LeanObject,
    mut v_inst_1853_: *mut crate::leanh::LeanObject,
    mut v_m_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_1857_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1858_: *mut crate::leanh::LeanObject,
    mut v_inst_1859_: *mut crate::leanh::LeanObject,
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
    mut v_m_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1863_: u8 = 0;
    let mut v_r_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(
        v_00_u03b1_1857_,
        v_00_u03b2_1858_,
        v_inst_1859_,
        v_inst_1860_,
        v_m_1861_,
        v_a_1862_,
    );
    crate::leanh::lean_dec_ref(v_m_1861_);
    v_r_1864_ = crate::leanh::lean_box((v_res_1863_) as usize);
    return v_r_1864_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(
    mut v_inst_1865_: *mut crate::leanh::LeanObject,
    mut v_inst_1866_: *mut crate::leanh::LeanObject,
    mut v_m_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1869_ = crate::leanh::lean_ctor_get(v_m_1867_, 1);
    crate::leanh::lean_inc(v_a_1868_);
    v___x_1870_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1866_, v_buckets_1869_, v_a_1868_);
    v___x_1871_ =
        l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1865_, v_a_1868_, v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(
    mut v_inst_1872_: *mut crate::leanh::LeanObject,
    mut v_inst_1873_: *mut crate::leanh::LeanObject,
    mut v_m_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(
        v_inst_1872_,
        v_inst_1873_,
        v_m_1874_,
        v_a_1875_,
    );
    crate::leanh::lean_dec_ref(v_m_1874_);
    return v_res_1876_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098(
    mut v_00_u03b1_1877_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1878_: *mut crate::leanh::LeanObject,
    mut v_inst_1879_: *mut crate::leanh::LeanObject,
    mut v_inst_1880_: *mut crate::leanh::LeanObject,
    mut v_inst_1881_: *mut crate::leanh::LeanObject,
    mut v_m_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_h_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(
        v_inst_1879_,
        v_inst_1881_,
        v_m_1882_,
        v_a_1883_,
    );
    return v___x_1885_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(
    mut v_00_u03b1_1886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1887_: *mut crate::leanh::LeanObject,
    mut v_inst_1888_: *mut crate::leanh::LeanObject,
    mut v_inst_1889_: *mut crate::leanh::LeanObject,
    mut v_inst_1890_: *mut crate::leanh::LeanObject,
    mut v_m_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
    mut v_h_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_m_1891_);
    return v_res_1894_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(
    mut v_inst_1895_: *mut crate::leanh::LeanObject,
    mut v_inst_1896_: *mut crate::leanh::LeanObject,
    mut v_m_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1899_ = crate::leanh::lean_ctor_get(v_m_1897_, 1);
    crate::leanh::lean_inc(v_a_1898_);
    v___x_1900_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1896_, v_buckets_1899_, v_a_1898_);
    v___x_1901_ =
        l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1895_, v_a_1898_, v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(
    mut v_inst_1902_: *mut crate::leanh::LeanObject,
    mut v_inst_1903_: *mut crate::leanh::LeanObject,
    mut v_m_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(
        v_inst_1902_,
        v_inst_1903_,
        v_m_1904_,
        v_a_1905_,
    );
    crate::leanh::lean_dec_ref(v_m_1904_);
    return v_res_1906_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(
    mut v_00_u03b1_1907_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1908_: *mut crate::leanh::LeanObject,
    mut v_inst_1909_: *mut crate::leanh::LeanObject,
    mut v_inst_1910_: *mut crate::leanh::LeanObject,
    mut v_m_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
    mut v_h_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(
        v_inst_1909_,
        v_inst_1910_,
        v_m_1911_,
        v_a_1912_,
    );
    return v___x_1914_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(
    mut v_00_u03b1_1915_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1916_: *mut crate::leanh::LeanObject,
    mut v_inst_1917_: *mut crate::leanh::LeanObject,
    mut v_inst_1918_: *mut crate::leanh::LeanObject,
    mut v_m_1919_: *mut crate::leanh::LeanObject,
    mut v_a_1920_: *mut crate::leanh::LeanObject,
    mut v_h_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(
        v_00_u03b1_1915_,
        v_00_u03b2_1916_,
        v_inst_1917_,
        v_inst_1918_,
        v_m_1919_,
        v_a_1920_,
        v_h_1921_,
    );
    crate::leanh::lean_dec_ref(v_m_1919_);
    return v_res_1922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
    mut v_inst_1923_: *mut crate::leanh::LeanObject,
    mut v_inst_1924_: *mut crate::leanh::LeanObject,
    mut v_m_1925_: *mut crate::leanh::LeanObject,
    mut v_a_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1927_ = crate::leanh::lean_ctor_get(v_m_1925_, 1);
    crate::leanh::lean_inc(v_a_1926_);
    v___x_1928_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1924_, v_buckets_1927_, v_a_1926_);
    v___x_1929_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(
        v_inst_1923_,
        v_a_1926_,
        v___x_1928_,
    );
    return v___x_1929_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(
    mut v_inst_1930_: *mut crate::leanh::LeanObject,
    mut v_inst_1931_: *mut crate::leanh::LeanObject,
    mut v_m_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
        v_inst_1930_,
        v_inst_1931_,
        v_m_1932_,
        v_a_1933_,
    );
    crate::leanh::lean_dec_ref(v_m_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(
    mut v_00_u03b1_1935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1936_: *mut crate::leanh::LeanObject,
    mut v_inst_1937_: *mut crate::leanh::LeanObject,
    mut v_inst_1938_: *mut crate::leanh::LeanObject,
    mut v_m_1939_: *mut crate::leanh::LeanObject,
    mut v_a_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
        v_inst_1937_,
        v_inst_1938_,
        v_m_1939_,
        v_a_1940_,
    );
    return v___x_1941_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(
    mut v_00_u03b1_1942_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1943_: *mut crate::leanh::LeanObject,
    mut v_inst_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_m_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(
        v_00_u03b1_1942_,
        v_00_u03b2_1943_,
        v_inst_1944_,
        v_inst_1945_,
        v_m_1946_,
        v_a_1947_,
    );
    crate::leanh::lean_dec_ref(v_m_1946_);
    return v_res_1948_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(
    mut v_inst_1949_: *mut crate::leanh::LeanObject,
    mut v_inst_1950_: *mut crate::leanh::LeanObject,
    mut v_m_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
    mut v_fallback_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1954_ = crate::leanh::lean_ctor_get(v_m_1951_, 1);
    crate::leanh::lean_inc(v_a_1952_);
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
    mut v_inst_1957_: *mut crate::leanh::LeanObject,
    mut v_inst_1958_: *mut crate::leanh::LeanObject,
    mut v_m_1959_: *mut crate::leanh::LeanObject,
    mut v_a_1960_: *mut crate::leanh::LeanObject,
    mut v_fallback_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(
        v_inst_1957_,
        v_inst_1958_,
        v_m_1959_,
        v_a_1960_,
        v_fallback_1961_,
    );
    crate::leanh::lean_dec_ref(v_fallback_1961_);
    crate::leanh::lean_dec_ref(v_m_1959_);
    return v_res_1962_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(
    mut v_00_u03b1_1963_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1964_: *mut crate::leanh::LeanObject,
    mut v_inst_1965_: *mut crate::leanh::LeanObject,
    mut v_inst_1966_: *mut crate::leanh::LeanObject,
    mut v_m_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_fallback_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1971_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1972_: *mut crate::leanh::LeanObject,
    mut v_inst_1973_: *mut crate::leanh::LeanObject,
    mut v_inst_1974_: *mut crate::leanh::LeanObject,
    mut v_m_1975_: *mut crate::leanh::LeanObject,
    mut v_a_1976_: *mut crate::leanh::LeanObject,
    mut v_fallback_1977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1978_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(
        v_00_u03b1_1971_,
        v_00_u03b2_1972_,
        v_inst_1973_,
        v_inst_1974_,
        v_m_1975_,
        v_a_1976_,
        v_fallback_1977_,
    );
    crate::leanh::lean_dec_ref(v_fallback_1977_);
    crate::leanh::lean_dec_ref(v_m_1975_);
    return v_res_1978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_inst_1980_: *mut crate::leanh::LeanObject,
    mut v_inst_1981_: *mut crate::leanh::LeanObject,
    mut v_m_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1984_ = crate::leanh::lean_ctor_get(v_m_1982_, 1);
    crate::leanh::lean_inc(v_a_1983_);
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
    mut v_inst_1987_: *mut crate::leanh::LeanObject,
    mut v_inst_1988_: *mut crate::leanh::LeanObject,
    mut v_inst_1989_: *mut crate::leanh::LeanObject,
    mut v_m_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(
        v_inst_1987_,
        v_inst_1988_,
        v_inst_1989_,
        v_m_1990_,
        v_a_1991_,
    );
    crate::leanh::lean_dec_ref(v_m_1990_);
    crate::leanh::lean_dec_ref(v_inst_1989_);
    return v_res_1992_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(
    mut v_00_u03b1_1993_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1994_: *mut crate::leanh::LeanObject,
    mut v_inst_1995_: *mut crate::leanh::LeanObject,
    mut v_inst_1996_: *mut crate::leanh::LeanObject,
    mut v_inst_1997_: *mut crate::leanh::LeanObject,
    mut v_m_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2001_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2002_: *mut crate::leanh::LeanObject,
    mut v_inst_2003_: *mut crate::leanh::LeanObject,
    mut v_inst_2004_: *mut crate::leanh::LeanObject,
    mut v_inst_2005_: *mut crate::leanh::LeanObject,
    mut v_m_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2008_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(
        v_00_u03b1_2001_,
        v_00_u03b2_2002_,
        v_inst_2003_,
        v_inst_2004_,
        v_inst_2005_,
        v_m_2006_,
        v_a_2007_,
    );
    crate::leanh::lean_dec_ref(v_m_2006_);
    crate::leanh::lean_dec_ref(v_inst_2005_);
    return v_res_2008_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(
    mut v_inst_2009_: *mut crate::leanh::LeanObject,
    mut v_inst_2010_: *mut crate::leanh::LeanObject,
    mut v_m_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
    mut v_fallback_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_2009_,
        v_inst_2010_,
        v_m_2011_,
        v_a_2012_,
    );
    if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
        crate::leanh::lean_inc(v_fallback_2013_);
        return v_fallback_2013_;
    } else {
        let mut v_val_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2015_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
        crate::leanh::lean_inc(v_val_2015_);
        crate::leanh::lean_dec_ref_known(v___x_2014_, 1);
        return v_val_2015_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_inst_2017_: *mut crate::leanh::LeanObject,
    mut v_m_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_fallback_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(
        v_inst_2016_,
        v_inst_2017_,
        v_m_2018_,
        v_a_2019_,
        v_fallback_2020_,
    );
    crate::leanh::lean_dec(v_fallback_2020_);
    crate::leanh::lean_dec_ref(v_m_2018_);
    return v_res_2021_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(
    mut v_00_u03b1_2022_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2023_: *mut crate::leanh::LeanObject,
    mut v_inst_2024_: *mut crate::leanh::LeanObject,
    mut v_inst_2025_: *mut crate::leanh::LeanObject,
    mut v_inst_2026_: *mut crate::leanh::LeanObject,
    mut v_m_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
    mut v_fallback_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2032_: *mut crate::leanh::LeanObject,
    mut v_inst_2033_: *mut crate::leanh::LeanObject,
    mut v_inst_2034_: *mut crate::leanh::LeanObject,
    mut v_inst_2035_: *mut crate::leanh::LeanObject,
    mut v_m_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
    mut v_fallback_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_fallback_2038_);
    crate::leanh::lean_dec_ref(v_m_2036_);
    return v_res_2039_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2;
    v___x_2044_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2045_ = crate::leanh::lean_unsigned_to_nat(22);
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
    mut v_inst_2049_: *mut crate::leanh::LeanObject,
    mut v_inst_2050_: *mut crate::leanh::LeanObject,
    mut v_m_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
    mut v_inst_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(
        v_inst_2049_,
        v_inst_2050_,
        v_m_2051_,
        v_a_2052_,
    );
    if crate::leanh::lean_obj_tag(v___x_2054_) == 0 {
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2055_ = crate::leanh::lean_obj_once(
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
        let mut v_val_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2057_ = crate::leanh::lean_ctor_get(v___x_2054_, 0);
        crate::leanh::lean_inc(v_val_2057_);
        crate::leanh::lean_dec_ref_known(v___x_2054_, 1);
        return v_val_2057_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(
    mut v_inst_2058_: *mut crate::leanh::LeanObject,
    mut v_inst_2059_: *mut crate::leanh::LeanObject,
    mut v_m_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_inst_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(
        v_inst_2058_,
        v_inst_2059_,
        v_m_2060_,
        v_a_2061_,
        v_inst_2062_,
    );
    crate::leanh::lean_dec(v_inst_2062_);
    crate::leanh::lean_dec_ref(v_m_2060_);
    return v_res_2063_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(
    mut v_00_u03b1_2064_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2065_: *mut crate::leanh::LeanObject,
    mut v_inst_2066_: *mut crate::leanh::LeanObject,
    mut v_inst_2067_: *mut crate::leanh::LeanObject,
    mut v_inst_2068_: *mut crate::leanh::LeanObject,
    mut v_m_2069_: *mut crate::leanh::LeanObject,
    mut v_a_2070_: *mut crate::leanh::LeanObject,
    mut v_inst_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2073_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2074_: *mut crate::leanh::LeanObject,
    mut v_inst_2075_: *mut crate::leanh::LeanObject,
    mut v_inst_2076_: *mut crate::leanh::LeanObject,
    mut v_inst_2077_: *mut crate::leanh::LeanObject,
    mut v_m_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_inst_2080_);
    crate::leanh::lean_dec_ref(v_m_2078_);
    return v_res_2081_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(
    mut v_inst_2082_: *mut crate::leanh::LeanObject,
    mut v_inst_2083_: *mut crate::leanh::LeanObject,
    mut v_m_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2086_ = crate::leanh::lean_ctor_get(v_m_2084_, 1);
    crate::leanh::lean_inc(v_a_2085_);
    v___x_2087_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_2083_, v_buckets_2086_, v_a_2085_);
    v___x_2088_ =
        l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_2082_, v_a_2085_, v___x_2087_);
    return v___x_2088_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(
    mut v_inst_2089_: *mut crate::leanh::LeanObject,
    mut v_inst_2090_: *mut crate::leanh::LeanObject,
    mut v_m_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(
        v_inst_2089_,
        v_inst_2090_,
        v_m_2091_,
        v_a_2092_,
    );
    crate::leanh::lean_dec_ref(v_m_2091_);
    return v_res_2093_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(
    mut v_00_u03b1_2094_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2095_: *mut crate::leanh::LeanObject,
    mut v_inst_2096_: *mut crate::leanh::LeanObject,
    mut v_inst_2097_: *mut crate::leanh::LeanObject,
    mut v_m_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_h_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(
        v_inst_2096_,
        v_inst_2097_,
        v_m_2098_,
        v_a_2099_,
    );
    return v___x_2101_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(
    mut v_00_u03b1_2102_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2103_: *mut crate::leanh::LeanObject,
    mut v_inst_2104_: *mut crate::leanh::LeanObject,
    mut v_inst_2105_: *mut crate::leanh::LeanObject,
    mut v_m_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_h_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(
        v_00_u03b1_2102_,
        v_00_u03b2_2103_,
        v_inst_2104_,
        v_inst_2105_,
        v_m_2106_,
        v_a_2107_,
        v_h_2108_,
    );
    crate::leanh::lean_dec_ref(v_m_2106_);
    return v_res_2109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(
    mut v_inst_2110_: *mut crate::leanh::LeanObject,
    mut v_inst_2111_: *mut crate::leanh::LeanObject,
    mut v_m_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_fallback_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_2110_,
        v_inst_2111_,
        v_m_2112_,
        v_a_2113_,
    );
    if crate::leanh::lean_obj_tag(v___x_2115_) == 0 {
        crate::leanh::lean_inc(v_fallback_2114_);
        return v_fallback_2114_;
    } else {
        let mut v_val_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2116_ = crate::leanh::lean_ctor_get(v___x_2115_, 0);
        crate::leanh::lean_inc(v_val_2116_);
        crate::leanh::lean_dec_ref_known(v___x_2115_, 1);
        return v_val_2116_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(
    mut v_inst_2117_: *mut crate::leanh::LeanObject,
    mut v_inst_2118_: *mut crate::leanh::LeanObject,
    mut v_m_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_fallback_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(
        v_inst_2117_,
        v_inst_2118_,
        v_m_2119_,
        v_a_2120_,
        v_fallback_2121_,
    );
    crate::leanh::lean_dec(v_fallback_2121_);
    crate::leanh::lean_dec_ref(v_m_2119_);
    return v_res_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(
    mut v_00_u03b1_2123_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2124_: *mut crate::leanh::LeanObject,
    mut v_inst_2125_: *mut crate::leanh::LeanObject,
    mut v_inst_2126_: *mut crate::leanh::LeanObject,
    mut v_m_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
    mut v_fallback_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2131_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2132_: *mut crate::leanh::LeanObject,
    mut v_inst_2133_: *mut crate::leanh::LeanObject,
    mut v_inst_2134_: *mut crate::leanh::LeanObject,
    mut v_m_2135_: *mut crate::leanh::LeanObject,
    mut v_a_2136_: *mut crate::leanh::LeanObject,
    mut v_fallback_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(
        v_00_u03b1_2131_,
        v_00_u03b2_2132_,
        v_inst_2133_,
        v_inst_2134_,
        v_m_2135_,
        v_a_2136_,
        v_fallback_2137_,
    );
    crate::leanh::lean_dec(v_fallback_2137_);
    crate::leanh::lean_dec_ref(v_m_2135_);
    return v_res_2138_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(
    mut v_inst_2139_: *mut crate::leanh::LeanObject,
    mut v_inst_2140_: *mut crate::leanh::LeanObject,
    mut v_inst_2141_: *mut crate::leanh::LeanObject,
    mut v_m_2142_: *mut crate::leanh::LeanObject,
    mut v_a_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(
        v_inst_2139_,
        v_inst_2140_,
        v_m_2142_,
        v_a_2143_,
    );
    if crate::leanh::lean_obj_tag(v___x_2144_) == 0 {
        let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2145_ = crate::leanh::lean_obj_once(
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
        let mut v_val_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2147_ = crate::leanh::lean_ctor_get(v___x_2144_, 0);
        crate::leanh::lean_inc(v_val_2147_);
        crate::leanh::lean_dec_ref_known(v___x_2144_, 1);
        return v_val_2147_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(
    mut v_inst_2148_: *mut crate::leanh::LeanObject,
    mut v_inst_2149_: *mut crate::leanh::LeanObject,
    mut v_inst_2150_: *mut crate::leanh::LeanObject,
    mut v_m_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(
        v_inst_2148_,
        v_inst_2149_,
        v_inst_2150_,
        v_m_2151_,
        v_a_2152_,
    );
    crate::leanh::lean_dec_ref(v_m_2151_);
    crate::leanh::lean_dec(v_inst_2150_);
    return v_res_2153_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(
    mut v_00_u03b1_2154_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2155_: *mut crate::leanh::LeanObject,
    mut v_inst_2156_: *mut crate::leanh::LeanObject,
    mut v_inst_2157_: *mut crate::leanh::LeanObject,
    mut v_inst_2158_: *mut crate::leanh::LeanObject,
    mut v_m_2159_: *mut crate::leanh::LeanObject,
    mut v_a_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2163_: *mut crate::leanh::LeanObject,
    mut v_inst_2164_: *mut crate::leanh::LeanObject,
    mut v_inst_2165_: *mut crate::leanh::LeanObject,
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_m_2167_: *mut crate::leanh::LeanObject,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(
        v_00_u03b1_2162_,
        v_00_u03b2_2163_,
        v_inst_2164_,
        v_inst_2165_,
        v_inst_2166_,
        v_m_2167_,
        v_a_2168_,
    );
    crate::leanh::lean_dec_ref(v_m_2167_);
    crate::leanh::lean_dec(v_inst_2166_);
    return v_res_2169_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(
    mut v_inst_2170_: *mut crate::leanh::LeanObject,
    mut v_inst_2171_: *mut crate::leanh::LeanObject,
    mut v_m_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
    mut v_b_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2175_: u8 = 0;
    let mut v_val_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v_val_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_unused_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2173_);
                crate::leanh::lean_inc_ref(v_inst_2171_);
                crate::leanh::lean_inc_ref(v_inst_2170_);
                v___x_2175_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2170_,
                    v_inst_2171_,
                    v_m_2172_,
                    v_a_2173_,
                );
                if v___x_2175_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2170_);
                    crate::leanh::lean_inc_ref(v_inst_2171_);
                    v_val_2176_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                        v_inst_2171_,
                        v_m_2172_,
                        v_a_2173_,
                        v_b_2174_,
                    );
                    v_size_2177_ = crate::leanh::lean_ctor_get(v_val_2176_, 0);
                    crate::leanh::lean_inc(v_size_2177_);
                    v_buckets_2178_ = crate::leanh::lean_ctor_get(v_val_2176_, 1);
                    crate::leanh::lean_inc_ref(v_buckets_2178_);
                    v___x_2179_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2180_ = lean_nat_mul(v_size_2177_, v___x_2179_);
                    v___x_2181_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2182_ = lean_nat_div(v___x_2180_, v___x_2181_);
                    crate::leanh::lean_dec(v___x_2180_);
                    v___x_2183_ = lean_array_get_size(v_buckets_2178_);
                    v___x_2184_ = lean_nat_dec_le(v___x_2182_, v___x_2183_);
                    crate::leanh::lean_dec(v___x_2182_);
                    if v___x_2184_ == 0 {
                        v_isSharedCheck_2192_ =
                            (!crate::leanh::lean_is_exclusive(v_val_2176_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v_unused_2193_ = crate::leanh::lean_ctor_get(v_val_2176_, 1);
                            crate::leanh::lean_dec(v_unused_2193_);
                            v_unused_2194_ = crate::leanh::lean_ctor_get(v_val_2176_, 0);
                            crate::leanh::lean_dec(v_unused_2194_);
                            v___x_2186_ = v_val_2176_;
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_2176_);
                            v___x_2186_ = crate::leanh::lean_box(0);
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_buckets_2178_);
                        crate::leanh::lean_dec(v_size_2177_);
                        crate::leanh::lean_dec_ref(v_inst_2171_);
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
                    crate::leanh::lean_ctor_set(v___x_2186_, 1, v_val_2188_);
                    v___x_2190_ = v___x_2186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_2177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_val_2188_);
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
    mut v_00_u03b1_2196_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2197_: *mut crate::leanh::LeanObject,
    mut v_inst_2198_: *mut crate::leanh::LeanObject,
    mut v_inst_2199_: *mut crate::leanh::LeanObject,
    mut v_m_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_b_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2204_: *mut crate::leanh::LeanObject,
    mut v_inst_2205_: *mut crate::leanh::LeanObject,
    mut v_m_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_b_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2209_: u8 = 0;
    let mut v_val_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v_val_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut v_unused_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2207_);
                crate::leanh::lean_inc_ref(v_inst_2205_);
                v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2204_,
                    v_inst_2205_,
                    v_m_2206_,
                    v_a_2207_,
                );
                if v___x_2209_ == 0 {
                    crate::leanh::lean_inc_ref(v_inst_2205_);
                    v_val_2210_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                        v_inst_2205_,
                        v_m_2206_,
                        v_a_2207_,
                        v_b_2208_,
                    );
                    v_size_2211_ = crate::leanh::lean_ctor_get(v_val_2210_, 0);
                    crate::leanh::lean_inc(v_size_2211_);
                    v_buckets_2212_ = crate::leanh::lean_ctor_get(v_val_2210_, 1);
                    crate::leanh::lean_inc_ref(v_buckets_2212_);
                    v___x_2213_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2214_ = lean_nat_mul(v_size_2211_, v___x_2213_);
                    v___x_2215_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2216_ = lean_nat_div(v___x_2214_, v___x_2215_);
                    crate::leanh::lean_dec(v___x_2214_);
                    v___x_2217_ = lean_array_get_size(v_buckets_2212_);
                    v___x_2218_ = lean_nat_dec_le(v___x_2216_, v___x_2217_);
                    crate::leanh::lean_dec(v___x_2216_);
                    if v___x_2218_ == 0 {
                        v_isSharedCheck_2226_ =
                            (!crate::leanh::lean_is_exclusive(v_val_2210_)) as u8;
                        if v_isSharedCheck_2226_ == 0 {
                            v_unused_2227_ = crate::leanh::lean_ctor_get(v_val_2210_, 1);
                            crate::leanh::lean_dec(v_unused_2227_);
                            v_unused_2228_ = crate::leanh::lean_ctor_get(v_val_2210_, 0);
                            crate::leanh::lean_dec(v_unused_2228_);
                            v___x_2220_ = v_val_2210_;
                            v_isShared_2221_ = v_isSharedCheck_2226_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_2210_);
                            v___x_2220_ = crate::leanh::lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2226_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_buckets_2212_);
                        crate::leanh::lean_dec(v_size_2211_);
                        crate::leanh::lean_dec_ref(v_inst_2205_);
                        return v_val_2210_;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2208_);
                    crate::leanh::lean_dec(v_a_2207_);
                    crate::leanh::lean_dec_ref(v_inst_2205_);
                    return v_m_2206_;
                }
            }
            1 => {
                v_val_2222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2205_,
                    v_buckets_2212_,
                );
                if v_isShared_2221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2220_, 1, v_val_2222_);
                    v___x_2224_ = v___x_2220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_size_2211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_val_2222_);
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
    mut v_00_u03b1_2229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut crate::leanh::LeanObject,
    mut v_inst_2231_: *mut crate::leanh::LeanObject,
    mut v_inst_2232_: *mut crate::leanh::LeanObject,
    mut v_m_2233_: *mut crate::leanh::LeanObject,
    mut v_a_2234_: *mut crate::leanh::LeanObject,
    mut v_b_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2237_: *mut crate::leanh::LeanObject,
    mut v_a_2238_: *mut crate::leanh::LeanObject,
    mut v_l_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ =
        l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_2237_, v_a_2238_, v_l_2239_);
    return v___x_2240_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(
    mut v_inst_2241_: *mut crate::leanh::LeanObject,
    mut v_inst_2242_: *mut crate::leanh::LeanObject,
    mut v_m_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2249_: u8 = 0;
    let mut v___f_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2245_ = crate::leanh::lean_ctor_get(v_m_2243_, 0);
                v_buckets_2246_ = crate::leanh::lean_ctor_get(v_m_2243_, 1);
                v_isSharedCheck_2257_ = (!crate::leanh::lean_is_exclusive(v_m_2243_)) as u8;
                if v_isSharedCheck_2257_ == 0 {
                    v___x_2248_ = v_m_2243_;
                    v_isShared_2249_ = v_isSharedCheck_2257_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2246_);
                    crate::leanh::lean_inc(v_size_2245_);
                    crate::leanh::lean_dec(v_m_2243_);
                    v___x_2248_ = crate::leanh::lean_box(0);
                    v_isShared_2249_ = v_isSharedCheck_2257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2244_);
                v___f_2250_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2250_, 0, v_inst_2241_);
                crate::leanh::lean_closure_set(v___f_2250_, 1, v_a_2244_);
                v___x_2251_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2252_ = lean_nat_sub(v_size_2245_, v___x_2251_);
                crate::leanh::lean_dec(v_size_2245_);
                v___x_2253_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_2242_,
                    v_buckets_2246_,
                    v_a_2244_,
                    v___f_2250_,
                );
                if v_isShared_2249_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2248_, 1, v___x_2253_);
                    crate::leanh::lean_ctor_set(v___x_2248_, 0, v___x_2252_);
                    v___x_2255_ = v___x_2248_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2253_);
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
    mut v_00_u03b1_2258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut crate::leanh::LeanObject,
    mut v_inst_2260_: *mut crate::leanh::LeanObject,
    mut v_inst_2261_: *mut crate::leanh::LeanObject,
    mut v_m_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(
        v_inst_2260_,
        v_inst_2261_,
        v_m_2262_,
        v_a_2263_,
    );
    return v___x_2264_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(
    mut v_inst_2265_: *mut crate::leanh::LeanObject,
    mut v_inst_2266_: *mut crate::leanh::LeanObject,
    mut v_m_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2269_: u8 = 0;
    crate::leanh::lean_inc(v_a_2268_);
    crate::leanh::lean_inc_ref(v_inst_2266_);
    crate::leanh::lean_inc_ref(v_inst_2265_);
    v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
        v_inst_2265_,
        v_inst_2266_,
        v_m_2267_,
        v_a_2268_,
    );
    if v___x_2269_ == 0 {
        crate::leanh::lean_dec(v_a_2268_);
        crate::leanh::lean_dec_ref(v_inst_2266_);
        crate::leanh::lean_dec_ref(v_inst_2265_);
        return v_m_2267_;
    } else {
        let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2272_: *mut crate::leanh::LeanObject,
    mut v_inst_2273_: *mut crate::leanh::LeanObject,
    mut v_inst_2274_: *mut crate::leanh::LeanObject,
    mut v_m_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(
        v_inst_2273_,
        v_inst_2274_,
        v_m_2275_,
        v_a_2276_,
    );
    return v___x_2277_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0(
    mut v_inst_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_f_2280_: *mut crate::leanh::LeanObject,
    mut v_l_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
        v_inst_2278_,
        v_a_2279_,
        v_f_2280_,
        v_l_2281_,
    );
    return v___x_2282_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(
    mut v_inst_2283_: *mut crate::leanh::LeanObject,
    mut v_inst_2284_: *mut crate::leanh::LeanObject,
    mut v_m_2285_: *mut crate::leanh::LeanObject,
    mut v_a_2286_: *mut crate::leanh::LeanObject,
    mut v_f_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v_val_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut v_unused_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___f_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2286_);
                crate::leanh::lean_inc_ref(v_inst_2284_);
                crate::leanh::lean_inc_ref(v_inst_2283_);
                v___x_2288_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2283_,
                    v_inst_2284_,
                    v_m_2285_,
                    v_a_2286_,
                );
                if v___x_2288_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2283_);
                    v___x_2289_ = crate::leanh::lean_box(0);
                    v___x_2290_ = crate::leanh::lean_apply_1(v_f_2287_, v___x_2289_);
                    if crate::leanh::lean_obj_tag(v___x_2290_) == 0 {
                        crate::leanh::lean_dec(v_a_2286_);
                        crate::leanh::lean_dec_ref(v_inst_2284_);
                        return v_m_2285_;
                    } else {
                        v_val_2291_ = crate::leanh::lean_ctor_get(v___x_2290_, 0);
                        crate::leanh::lean_inc(v_val_2291_);
                        crate::leanh::lean_dec_ref_known(v___x_2290_, 1);
                        crate::leanh::lean_inc_ref(v_inst_2284_);
                        v_val_2292_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                            v_inst_2284_,
                            v_m_2285_,
                            v_a_2286_,
                            v_val_2291_,
                        );
                        v_size_2293_ = crate::leanh::lean_ctor_get(v_val_2292_, 0);
                        crate::leanh::lean_inc(v_size_2293_);
                        v_buckets_2294_ = crate::leanh::lean_ctor_get(v_val_2292_, 1);
                        crate::leanh::lean_inc_ref(v_buckets_2294_);
                        v___x_2295_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_2296_ = lean_nat_mul(v_size_2293_, v___x_2295_);
                        v___x_2297_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2298_ = lean_nat_div(v___x_2296_, v___x_2297_);
                        crate::leanh::lean_dec(v___x_2296_);
                        v___x_2299_ = lean_array_get_size(v_buckets_2294_);
                        v___x_2300_ = lean_nat_dec_le(v___x_2298_, v___x_2299_);
                        crate::leanh::lean_dec(v___x_2298_);
                        if v___x_2300_ == 0 {
                            v_isSharedCheck_2308_ =
                                (!crate::leanh::lean_is_exclusive(v_val_2292_)) as u8;
                            if v_isSharedCheck_2308_ == 0 {
                                v_unused_2309_ = crate::leanh::lean_ctor_get(v_val_2292_, 1);
                                crate::leanh::lean_dec(v_unused_2309_);
                                v_unused_2310_ = crate::leanh::lean_ctor_get(v_val_2292_, 0);
                                crate::leanh::lean_dec(v_unused_2310_);
                                v___x_2302_ = v_val_2292_;
                                v_isShared_2303_ = v_isSharedCheck_2308_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_2292_);
                                v___x_2302_ = crate::leanh::lean_box(0);
                                v_isShared_2303_ = v_isSharedCheck_2308_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_buckets_2294_);
                            crate::leanh::lean_dec(v_size_2293_);
                            crate::leanh::lean_dec_ref(v_inst_2284_);
                            return v_val_2292_;
                        }
                    }
                } else {
                    v_size_2311_ = crate::leanh::lean_ctor_get(v_m_2285_, 0);
                    v_buckets_2312_ = crate::leanh::lean_ctor_get(v_m_2285_, 1);
                    v_isSharedCheck_2328_ = (!crate::leanh::lean_is_exclusive(v_m_2285_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2314_ = v_m_2285_;
                        v_isShared_2315_ = v_isSharedCheck_2328_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buckets_2312_);
                        crate::leanh::lean_inc(v_size_2311_);
                        crate::leanh::lean_dec(v_m_2285_);
                        v___x_2314_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_2302_, 1, v_val_2304_);
                    v___x_2306_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_size_2293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_val_2304_);
                    v___x_2306_ = v_reuseFailAlloc_2307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2306_;
            }
            3 => {
                crate::leanh::lean_inc_n(v_a_2286_, 2);
                crate::leanh::lean_inc_ref(v_inst_2283_);
                v___f_2316_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2316_, 0, v_inst_2283_);
                crate::leanh::lean_closure_set(v___f_2316_, 1, v_a_2286_);
                crate::leanh::lean_closure_set(v___f_2316_, 2, v_f_2287_);
                crate::leanh::lean_inc_ref(v_inst_2284_);
                v_buckets_x27_2317_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_2284_,
                    v_buckets_2312_,
                    v_a_2286_,
                    v___f_2316_,
                );
                crate::leanh::lean_inc_ref(v_buckets_x27_2317_);
                v___x_2318_ =
                    l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_2317_);
                v___x_2319_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2283_,
                    v_inst_2284_,
                    v___x_2318_,
                    v_a_2286_,
                );
                crate::leanh::lean_dec_ref(v___x_2318_);
                if v___x_2319_ == 0 {
                    v___x_2320_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2321_ = lean_nat_sub(v_size_2311_, v___x_2320_);
                    crate::leanh::lean_dec(v_size_2311_);
                    if v_isShared_2315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2317_);
                        crate::leanh::lean_ctor_set(v___x_2314_, 0, v___x_2321_);
                        v___x_2323_ = v___x_2314_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_buckets_x27_2317_);
                        v___x_2323_ = v_reuseFailAlloc_2324_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2314_, 1, v_buckets_x27_2317_);
                        v___x_2326_ = v___x_2314_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_size_2311_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_buckets_x27_2317_);
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
    mut v_00_u03b1_2329_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2330_: *mut crate::leanh::LeanObject,
    mut v_inst_2331_: *mut crate::leanh::LeanObject,
    mut v_inst_2332_: *mut crate::leanh::LeanObject,
    mut v_inst_2333_: *mut crate::leanh::LeanObject,
    mut v_m_2334_: *mut crate::leanh::LeanObject,
    mut v_a_2335_: *mut crate::leanh::LeanObject,
    mut v_f_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_2338_: *mut crate::leanh::LeanObject,
    mut v_x_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2339_) == 0 {
                    crate::leanh::lean_dec(v_f_2338_);
                    return v_x_2339_;
                } else {
                    v_val_2340_ = crate::leanh::lean_ctor_get(v_x_2339_, 0);
                    v_isSharedCheck_2348_ = (!crate::leanh::lean_is_exclusive(v_x_2339_)) as u8;
                    if v_isSharedCheck_2348_ == 0 {
                        v___x_2342_ = v_x_2339_;
                        v_isShared_2343_ = v_isSharedCheck_2348_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2340_);
                        crate::leanh::lean_dec(v_x_2339_);
                        v___x_2342_ = crate::leanh::lean_box(0);
                        v_isShared_2343_ = v_isSharedCheck_2348_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2344_ = crate::leanh::lean_apply_1(v_f_2338_, v_val_2340_);
                if v_isShared_2343_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2342_, 0, v___x_2344_);
                    v___x_2346_ = v___x_2342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
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
    mut v_inst_2349_: *mut crate::leanh::LeanObject,
    mut v_inst_2350_: *mut crate::leanh::LeanObject,
    mut v_m_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v_f_2353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2354_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2354_, 0, v_f_2353_);
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
    mut v_00_u03b1_2356_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2357_: *mut crate::leanh::LeanObject,
    mut v_inst_2358_: *mut crate::leanh::LeanObject,
    mut v_inst_2359_: *mut crate::leanh::LeanObject,
    mut v_inst_2360_: *mut crate::leanh::LeanObject,
    mut v_m_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_f_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2365_: *mut crate::leanh::LeanObject,
    mut v_a_2366_: *mut crate::leanh::LeanObject,
    mut v_f_2367_: *mut crate::leanh::LeanObject,
    mut v_l_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
        v_inst_2365_,
        v_a_2366_,
        v_f_2367_,
        v_l_2368_,
    );
    return v___x_2369_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(
    mut v_inst_2370_: *mut crate::leanh::LeanObject,
    mut v_inst_2371_: *mut crate::leanh::LeanObject,
    mut v_m_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
    mut v_f_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v_val_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_unused_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___f_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2373_);
                crate::leanh::lean_inc_ref(v_inst_2371_);
                crate::leanh::lean_inc_ref(v_inst_2370_);
                v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2370_,
                    v_inst_2371_,
                    v_m_2372_,
                    v_a_2373_,
                );
                if v___x_2375_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2370_);
                    v___x_2376_ = crate::leanh::lean_box(0);
                    v___x_2377_ = crate::leanh::lean_apply_1(v_f_2374_, v___x_2376_);
                    if crate::leanh::lean_obj_tag(v___x_2377_) == 0 {
                        crate::leanh::lean_dec(v_a_2373_);
                        crate::leanh::lean_dec_ref(v_inst_2371_);
                        return v_m_2372_;
                    } else {
                        v_val_2378_ = crate::leanh::lean_ctor_get(v___x_2377_, 0);
                        crate::leanh::lean_inc(v_val_2378_);
                        crate::leanh::lean_dec_ref_known(v___x_2377_, 1);
                        crate::leanh::lean_inc_ref(v_inst_2371_);
                        v_val_2379_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(
                            v_inst_2371_,
                            v_m_2372_,
                            v_a_2373_,
                            v_val_2378_,
                        );
                        v_size_2380_ = crate::leanh::lean_ctor_get(v_val_2379_, 0);
                        crate::leanh::lean_inc(v_size_2380_);
                        v_buckets_2381_ = crate::leanh::lean_ctor_get(v_val_2379_, 1);
                        crate::leanh::lean_inc_ref(v_buckets_2381_);
                        v___x_2382_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_2383_ = lean_nat_mul(v_size_2380_, v___x_2382_);
                        v___x_2384_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2385_ = lean_nat_div(v___x_2383_, v___x_2384_);
                        crate::leanh::lean_dec(v___x_2383_);
                        v___x_2386_ = lean_array_get_size(v_buckets_2381_);
                        v___x_2387_ = lean_nat_dec_le(v___x_2385_, v___x_2386_);
                        crate::leanh::lean_dec(v___x_2385_);
                        if v___x_2387_ == 0 {
                            v_isSharedCheck_2395_ =
                                (!crate::leanh::lean_is_exclusive(v_val_2379_)) as u8;
                            if v_isSharedCheck_2395_ == 0 {
                                v_unused_2396_ = crate::leanh::lean_ctor_get(v_val_2379_, 1);
                                crate::leanh::lean_dec(v_unused_2396_);
                                v_unused_2397_ = crate::leanh::lean_ctor_get(v_val_2379_, 0);
                                crate::leanh::lean_dec(v_unused_2397_);
                                v___x_2389_ = v_val_2379_;
                                v_isShared_2390_ = v_isSharedCheck_2395_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_2379_);
                                v___x_2389_ = crate::leanh::lean_box(0);
                                v_isShared_2390_ = v_isSharedCheck_2395_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_buckets_2381_);
                            crate::leanh::lean_dec(v_size_2380_);
                            crate::leanh::lean_dec_ref(v_inst_2371_);
                            return v_val_2379_;
                        }
                    }
                } else {
                    v_size_2398_ = crate::leanh::lean_ctor_get(v_m_2372_, 0);
                    v_buckets_2399_ = crate::leanh::lean_ctor_get(v_m_2372_, 1);
                    v_isSharedCheck_2415_ = (!crate::leanh::lean_is_exclusive(v_m_2372_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2401_ = v_m_2372_;
                        v_isShared_2402_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buckets_2399_);
                        crate::leanh::lean_inc(v_size_2398_);
                        crate::leanh::lean_dec(v_m_2372_);
                        v___x_2401_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_2389_, 1, v_val_2391_);
                    v___x_2393_ = v___x_2389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_size_2380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_val_2391_);
                    v___x_2393_ = v_reuseFailAlloc_2394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2393_;
            }
            3 => {
                crate::leanh::lean_inc_n(v_a_2373_, 2);
                crate::leanh::lean_inc_ref(v_inst_2370_);
                v___f_2403_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2403_, 0, v_inst_2370_);
                crate::leanh::lean_closure_set(v___f_2403_, 1, v_a_2373_);
                crate::leanh::lean_closure_set(v___f_2403_, 2, v_f_2374_);
                crate::leanh::lean_inc_ref(v_inst_2371_);
                v_buckets_x27_2404_ = l_Std_DHashMap_Internal_updateBucket___redArg(
                    v_inst_2371_,
                    v_buckets_2399_,
                    v_a_2373_,
                    v___f_2403_,
                );
                crate::leanh::lean_inc_ref(v_buckets_x27_2404_);
                v___x_2405_ =
                    l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_2404_);
                v___x_2406_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(
                    v_inst_2370_,
                    v_inst_2371_,
                    v___x_2405_,
                    v_a_2373_,
                );
                crate::leanh::lean_dec_ref(v___x_2405_);
                if v___x_2406_ == 0 {
                    v___x_2407_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2408_ = lean_nat_sub(v_size_2398_, v___x_2407_);
                    crate::leanh::lean_dec(v_size_2398_);
                    if v_isShared_2402_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2401_, 1, v_buckets_x27_2404_);
                        crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2408_);
                        v___x_2410_ = v___x_2401_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_buckets_x27_2404_);
                        v___x_2410_ = v_reuseFailAlloc_2411_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2402_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2401_, 1, v_buckets_x27_2404_);
                        v___x_2413_ = v___x_2401_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_size_2398_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_buckets_x27_2404_);
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
    mut v_00_u03b1_2416_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2417_: *mut crate::leanh::LeanObject,
    mut v_inst_2418_: *mut crate::leanh::LeanObject,
    mut v_inst_2419_: *mut crate::leanh::LeanObject,
    mut v_m_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
    mut v_f_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_2424_: *mut crate::leanh::LeanObject,
    mut v_option_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2429_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_option_2425_) == 0 {
                    crate::leanh::lean_dec(v_f_2424_);
                    return v_option_2425_;
                } else {
                    v_val_2426_ = crate::leanh::lean_ctor_get(v_option_2425_, 0);
                    v_isSharedCheck_2434_ =
                        (!crate::leanh::lean_is_exclusive(v_option_2425_)) as u8;
                    if v_isSharedCheck_2434_ == 0 {
                        v___x_2428_ = v_option_2425_;
                        v_isShared_2429_ = v_isSharedCheck_2434_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2426_);
                        crate::leanh::lean_dec(v_option_2425_);
                        v___x_2428_ = crate::leanh::lean_box(0);
                        v_isShared_2429_ = v_isSharedCheck_2434_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2430_ = crate::leanh::lean_apply_1(v_f_2424_, v_val_2426_);
                if v_isShared_2429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2428_, 0, v___x_2430_);
                    v___x_2432_ = v___x_2428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
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
    mut v_inst_2435_: *mut crate::leanh::LeanObject,
    mut v_inst_2436_: *mut crate::leanh::LeanObject,
    mut v_m_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_f_2439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2440_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2440_, 0, v_f_2439_);
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
    mut v_00_u03b1_2442_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2443_: *mut crate::leanh::LeanObject,
    mut v_inst_2444_: *mut crate::leanh::LeanObject,
    mut v_inst_2445_: *mut crate::leanh::LeanObject,
    mut v_m_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_f_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_2450_: *mut crate::leanh::LeanObject,
    mut v_acc_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2452_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_2450_);
                    return v_acc_2451_;
                } else {
                    v_key_2453_ = crate::leanh::lean_ctor_get(v_a_2452_, 0);
                    v_value_2454_ = crate::leanh::lean_ctor_get(v_a_2452_, 1);
                    v_tail_2455_ = crate::leanh::lean_ctor_get(v_a_2452_, 2);
                    v_isSharedCheck_2466_ = (!crate::leanh::lean_is_exclusive(v_a_2452_)) as u8;
                    if v_isSharedCheck_2466_ == 0 {
                        v___x_2457_ = v_a_2452_;
                        v_isShared_2458_ = v_isSharedCheck_2466_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2455_);
                        crate::leanh::lean_inc(v_value_2454_);
                        crate::leanh::lean_inc(v_key_2453_);
                        crate::leanh::lean_dec(v_a_2452_);
                        v___x_2457_ = crate::leanh::lean_box(0);
                        v_isShared_2458_ = v_isSharedCheck_2466_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_2450_);
                crate::leanh::lean_inc(v_key_2453_);
                v___x_2459_ = crate::leanh::lean_apply_2(v_f_2450_, v_key_2453_, v_value_2454_);
                if crate::leanh::lean_obj_tag(v___x_2459_) == 0 {
                    crate::leanh::lean_del_object(v___x_2457_);
                    crate::leanh::lean_dec(v_key_2453_);
                    v_a_2452_ = v_tail_2455_;
                    state = 0;
                    continue;
                } else {
                    v_val_2461_ = crate::leanh::lean_ctor_get(v___x_2459_, 0);
                    crate::leanh::lean_inc(v_val_2461_);
                    crate::leanh::lean_dec_ref_known(v___x_2459_, 1);
                    if v_isShared_2458_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2457_, 2, v_acc_2451_);
                        crate::leanh::lean_ctor_set(v___x_2457_, 1, v_val_2461_);
                        v___x_2463_ = v___x_2457_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2465_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_key_2453_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_val_2461_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_acc_2451_);
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
    mut v_f_2467_: *mut crate::leanh::LeanObject,
    mut v_l_2468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = crate::leanh::lean_box(0);
    v___x_2470_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_2467_, v___x_2469_, v_l_2468_);
    return v___x_2470_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(
    mut v_m_2471_: *mut crate::leanh::LeanObject,
    mut v_f_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2473_ = crate::leanh::lean_ctor_get(v_m_2471_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2473_);
    crate::leanh::lean_dec_ref(v_m_2471_);
    v___f_2474_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2474_, 0, v_f_2472_);
    v___x_2475_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_2473_, v___f_2474_);
    v___x_2476_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(
    mut v_00_u03b1_2477_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2478_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2479_: *mut crate::leanh::LeanObject,
    mut v_m_2480_: *mut crate::leanh::LeanObject,
    mut v_f_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(v_m_2480_, v_f_2481_);
    return v___x_2482_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(
    mut v_00_u03b1_2483_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2485_: *mut crate::leanh::LeanObject,
    mut v_f_2486_: *mut crate::leanh::LeanObject,
    mut v_acc_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_2486_, v_acc_2487_, v_a_2488_);
    return v___x_2489_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(
    mut v_f_2490_: *mut crate::leanh::LeanObject,
    mut v_acc_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2492_) == 0 {
                    crate::leanh::lean_dec(v_f_2490_);
                    return v_acc_2491_;
                } else {
                    v_key_2493_ = crate::leanh::lean_ctor_get(v_a_2492_, 0);
                    v_value_2494_ = crate::leanh::lean_ctor_get(v_a_2492_, 1);
                    v_tail_2495_ = crate::leanh::lean_ctor_get(v_a_2492_, 2);
                    v_isSharedCheck_2504_ = (!crate::leanh::lean_is_exclusive(v_a_2492_)) as u8;
                    if v_isSharedCheck_2504_ == 0 {
                        v___x_2497_ = v_a_2492_;
                        v_isShared_2498_ = v_isSharedCheck_2504_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2495_);
                        crate::leanh::lean_inc(v_value_2494_);
                        crate::leanh::lean_inc(v_key_2493_);
                        crate::leanh::lean_dec(v_a_2492_);
                        v___x_2497_ = crate::leanh::lean_box(0);
                        v_isShared_2498_ = v_isSharedCheck_2504_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_2490_);
                crate::leanh::lean_inc(v_key_2493_);
                v___x_2499_ = crate::leanh::lean_apply_2(v_f_2490_, v_key_2493_, v_value_2494_);
                if v_isShared_2498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2497_, 2, v_acc_2491_);
                    crate::leanh::lean_ctor_set(v___x_2497_, 1, v___x_2499_);
                    v___x_2501_ = v___x_2497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_key_2493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_acc_2491_);
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
    mut v_f_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = crate::leanh::lean_box(0);
    v___x_2508_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_2505_, v___x_2507_, v___y_2506_);
    return v___x_2508_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(
    mut v_m_2509_: *mut crate::leanh::LeanObject,
    mut v_f_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___f_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2511_ = crate::leanh::lean_ctor_get(v_m_2509_, 0);
                v_buckets_2512_ = crate::leanh::lean_ctor_get(v_m_2509_, 1);
                v_isSharedCheck_2521_ = (!crate::leanh::lean_is_exclusive(v_m_2509_)) as u8;
                if v_isSharedCheck_2521_ == 0 {
                    v___x_2514_ = v_m_2509_;
                    v_isShared_2515_ = v_isSharedCheck_2521_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2512_);
                    crate::leanh::lean_inc(v_size_2511_);
                    crate::leanh::lean_dec(v_m_2509_);
                    v___x_2514_ = crate::leanh::lean_box(0);
                    v_isShared_2515_ = v_isSharedCheck_2521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2516_ = crate::leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2516_, 0, v_f_2510_);
                v___x_2517_ =
                    l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_2512_, v___f_2516_);
                if v_isShared_2515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2514_, 1, v___x_2517_);
                    v___x_2519_ = v___x_2514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_size_2511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2517_);
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
    mut v_00_u03b1_2522_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2524_: *mut crate::leanh::LeanObject,
    mut v_m_2525_: *mut crate::leanh::LeanObject,
    mut v_f_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(v_m_2525_, v_f_2526_);
    return v___x_2527_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(
    mut v_00_u03b1_2528_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2529_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_2530_: *mut crate::leanh::LeanObject,
    mut v_f_2531_: *mut crate::leanh::LeanObject,
    mut v_acc_2532_: *mut crate::leanh::LeanObject,
    mut v_a_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2534_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_2531_, v_acc_2532_, v_a_2533_);
    return v___x_2534_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(
    mut v_f_2535_: *mut crate::leanh::LeanObject,
    mut v_acc_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2543_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2537_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_2535_);
                    return v_acc_2536_;
                } else {
                    v_key_2538_ = crate::leanh::lean_ctor_get(v_a_2537_, 0);
                    v_value_2539_ = crate::leanh::lean_ctor_get(v_a_2537_, 1);
                    v_tail_2540_ = crate::leanh::lean_ctor_get(v_a_2537_, 2);
                    v_isSharedCheck_2551_ = (!crate::leanh::lean_is_exclusive(v_a_2537_)) as u8;
                    if v_isSharedCheck_2551_ == 0 {
                        v___x_2542_ = v_a_2537_;
                        v_isShared_2543_ = v_isSharedCheck_2551_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2540_);
                        crate::leanh::lean_inc(v_value_2539_);
                        crate::leanh::lean_inc(v_key_2538_);
                        crate::leanh::lean_dec(v_a_2537_);
                        v___x_2542_ = crate::leanh::lean_box(0);
                        v_isShared_2543_ = v_isSharedCheck_2551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_2535_);
                crate::leanh::lean_inc(v_value_2539_);
                crate::leanh::lean_inc(v_key_2538_);
                v___x_2544_ = crate::leanh::lean_apply_2(v_f_2535_, v_key_2538_, v_value_2539_);
                v___x_2545_ = (crate::leanh::lean_unbox(v___x_2544_) as u8);
                if v___x_2545_ == 0 {
                    crate::leanh::lean_del_object(v___x_2542_);
                    crate::leanh::lean_dec(v_value_2539_);
                    crate::leanh::lean_dec(v_key_2538_);
                    v_a_2537_ = v_tail_2540_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_2543_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2542_, 2, v_acc_2536_);
                        v___x_2548_ = v___x_2542_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2550_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_key_2538_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_value_2539_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_acc_2536_);
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
    mut v_f_2552_: *mut crate::leanh::LeanObject,
    mut v_l_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = crate::leanh::lean_box(0);
    v___x_2555_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_2552_, v___x_2554_, v_l_2553_);
    return v___x_2555_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(
    mut v_m_2556_: *mut crate::leanh::LeanObject,
    mut v_f_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2558_ = crate::leanh::lean_ctor_get(v_m_2556_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2558_);
    crate::leanh::lean_dec_ref(v_m_2556_);
    v___f_2559_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2559_, 0, v_f_2557_);
    v___x_2560_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_2558_, v___f_2559_);
    v___x_2561_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_2560_);
    return v___x_2561_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(
    mut v_00_u03b1_2562_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2563_: *mut crate::leanh::LeanObject,
    mut v_m_2564_: *mut crate::leanh::LeanObject,
    mut v_f_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_2564_, v_f_2565_);
    return v___x_2566_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(
    mut v_00_u03b1_2567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2568_: *mut crate::leanh::LeanObject,
    mut v_f_2569_: *mut crate::leanh::LeanObject,
    mut v_acc_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_2569_, v_acc_2570_, v_a_2571_);
    return v___x_2572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(
    mut v_inst_2573_: *mut crate::leanh::LeanObject,
    mut v_inst_2574_: *mut crate::leanh::LeanObject,
    mut v_m_2575_: *mut crate::leanh::LeanObject,
    mut v_l_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_2576_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2574_);
                    crate::leanh::lean_dec_ref(v_inst_2573_);
                    return v_m_2575_;
                } else {
                    v_head_2577_ = crate::leanh::lean_ctor_get(v_l_2576_, 0);
                    crate::leanh::lean_inc(v_head_2577_);
                    v_tail_2578_ = crate::leanh::lean_ctor_get(v_l_2576_, 1);
                    crate::leanh::lean_inc(v_tail_2578_);
                    crate::leanh::lean_dec_ref_known(v_l_2576_, 2);
                    v_fst_2579_ = crate::leanh::lean_ctor_get(v_head_2577_, 0);
                    crate::leanh::lean_inc(v_fst_2579_);
                    v_snd_2580_ = crate::leanh::lean_ctor_get(v_head_2577_, 1);
                    crate::leanh::lean_inc(v_snd_2580_);
                    crate::leanh::lean_dec(v_head_2577_);
                    crate::leanh::lean_inc_ref(v_inst_2574_);
                    crate::leanh::lean_inc_ref(v_inst_2573_);
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
    mut v_00_u03b1_2583_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2584_: *mut crate::leanh::LeanObject,
    mut v_inst_2585_: *mut crate::leanh::LeanObject,
    mut v_inst_2586_: *mut crate::leanh::LeanObject,
    mut v_m_2587_: *mut crate::leanh::LeanObject,
    mut v_l_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(
        v_inst_2585_,
        v_inst_2586_,
        v_m_2587_,
        v_l_2588_,
    );
    return v___x_2589_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(
    mut v_inst_2590_: *mut crate::leanh::LeanObject,
    mut v_inst_2591_: *mut crate::leanh::LeanObject,
    mut v_m_2592_: *mut crate::leanh::LeanObject,
    mut v_l_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_2593_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2591_);
                    crate::leanh::lean_dec_ref(v_inst_2590_);
                    return v_m_2592_;
                } else {
                    v_head_2594_ = crate::leanh::lean_ctor_get(v_l_2593_, 0);
                    crate::leanh::lean_inc(v_head_2594_);
                    v_tail_2595_ = crate::leanh::lean_ctor_get(v_l_2593_, 1);
                    crate::leanh::lean_inc(v_tail_2595_);
                    crate::leanh::lean_dec_ref_known(v_l_2593_, 2);
                    crate::leanh::lean_inc_ref(v_inst_2591_);
                    crate::leanh::lean_inc_ref(v_inst_2590_);
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
    mut v_00_u03b1_2598_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2599_: *mut crate::leanh::LeanObject,
    mut v_inst_2600_: *mut crate::leanh::LeanObject,
    mut v_inst_2601_: *mut crate::leanh::LeanObject,
    mut v_m_2602_: *mut crate::leanh::LeanObject,
    mut v_l_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(
        v_inst_2600_,
        v_inst_2601_,
        v_m_2602_,
        v_l_2603_,
    );
    return v___x_2604_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(
    mut v_inst_2605_: *mut crate::leanh::LeanObject,
    mut v_inst_2606_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2607_: *mut crate::leanh::LeanObject,
    mut v___x_2608_: u8,
    mut v_k_2609_: *mut crate::leanh::LeanObject,
    mut v_x_2610_: *mut crate::leanh::LeanObject,
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
    mut v_inst_2613_: *mut crate::leanh::LeanObject,
    mut v_inst_2614_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2615_: *mut crate::leanh::LeanObject,
    mut v___x_2616_: *mut crate::leanh::LeanObject,
    mut v_k_2617_: *mut crate::leanh::LeanObject,
    mut v_x_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_52__boxed_2619_: u8 = 0;
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_52__boxed_2619_ = (crate::leanh::lean_unbox(v___x_2616_) as u8);
    v_res_2620_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(
        v_inst_2613_,
        v_inst_2614_,
        v_m_u2082_2615_,
        v___x_52__boxed_2619_,
        v_k_2617_,
        v_x_2618_,
    );
    crate::leanh::lean_dec(v_x_2618_);
    crate::leanh::lean_dec_ref(v_m_u2082_2615_);
    v_r_2621_ = crate::leanh::lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(
    mut v_inst_2645_: *mut crate::leanh::LeanObject,
    mut v_inst_2646_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2647_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    v_size_2649_ = crate::leanh::lean_ctor_get(v_m_u2081_2647_, 0);
    v_size_2650_ = crate::leanh::lean_ctor_get(v_m_u2082_2648_, 0);
    v_buckets_2651_ = crate::leanh::lean_ctor_get(v_m_u2082_2648_, 1);
    v___x_2652_ = lean_nat_dec_le(v_size_2649_, v_size_2650_);
    if v___x_2652_ == 0 {
        let mut v___f_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_2651_);
        crate::leanh::lean_dec_ref(v_m_u2082_2648_);
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
        let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2656_ = crate::leanh::lean_box((v___x_2652_) as usize);
        v___f_2657_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_2657_, 0, v_inst_2645_);
        crate::leanh::lean_closure_set(v___f_2657_, 1, v_inst_2646_);
        crate::leanh::lean_closure_set(v___f_2657_, 2, v_m_u2082_2648_);
        crate::leanh::lean_closure_set(v___f_2657_, 3, v___x_2656_);
        v___x_2658_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_u2081_2647_, v___f_2657_);
        return v___x_2658_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(
    mut v_00_u03b1_2659_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2660_: *mut crate::leanh::LeanObject,
    mut v_inst_2661_: *mut crate::leanh::LeanObject,
    mut v_inst_2662_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2663_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(
        v_inst_2661_,
        v_inst_2662_,
        v_m_u2081_2663_,
        v_m_u2082_2664_,
    );
    return v___x_2665_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(
    mut v_inst_2666_: *mut crate::leanh::LeanObject,
    mut v_inst_2667_: *mut crate::leanh::LeanObject,
    mut v_m_2668_: *mut crate::leanh::LeanObject,
    mut v_l_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_2669_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2667_);
                    crate::leanh::lean_dec_ref(v_inst_2666_);
                    return v_m_2668_;
                } else {
                    v_head_2670_ = crate::leanh::lean_ctor_get(v_l_2669_, 0);
                    crate::leanh::lean_inc(v_head_2670_);
                    v_tail_2671_ = crate::leanh::lean_ctor_get(v_l_2669_, 1);
                    crate::leanh::lean_inc(v_tail_2671_);
                    crate::leanh::lean_dec_ref_known(v_l_2669_, 2);
                    v_fst_2672_ = crate::leanh::lean_ctor_get(v_head_2670_, 0);
                    crate::leanh::lean_inc(v_fst_2672_);
                    v_snd_2673_ = crate::leanh::lean_ctor_get(v_head_2670_, 1);
                    crate::leanh::lean_inc(v_snd_2673_);
                    crate::leanh::lean_dec(v_head_2670_);
                    crate::leanh::lean_inc_ref(v_inst_2667_);
                    crate::leanh::lean_inc_ref(v_inst_2666_);
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
    mut v_00_u03b1_2676_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2677_: *mut crate::leanh::LeanObject,
    mut v_inst_2678_: *mut crate::leanh::LeanObject,
    mut v_inst_2679_: *mut crate::leanh::LeanObject,
    mut v_m_2680_: *mut crate::leanh::LeanObject,
    mut v_l_2681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(
        v_inst_2678_,
        v_inst_2679_,
        v_m_2680_,
        v_l_2681_,
    );
    return v___x_2682_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(
    mut v_inst_2683_: *mut crate::leanh::LeanObject,
    mut v_inst_2684_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2685_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    v_size_2687_ = crate::leanh::lean_ctor_get(v_m_u2081_2685_, 0);
    v_buckets_2688_ = crate::leanh::lean_ctor_get(v_m_u2081_2685_, 1);
    v_size_2689_ = crate::leanh::lean_ctor_get(v_m_u2082_2686_, 0);
    v_buckets_2690_ = crate::leanh::lean_ctor_get(v_m_u2082_2686_, 1);
    v___x_2691_ = lean_nat_dec_le(v_size_2687_, v_size_2689_);
    if v___x_2691_ == 0 {
        let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_2690_);
        crate::leanh::lean_dec_ref(v_m_u2082_2686_);
        v___x_2692_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_2690_);
        v___x_2693_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(
            v_inst_2683_,
            v_inst_2684_,
            v_m_u2081_2685_,
            v___x_2692_,
        );
        return v___x_2693_;
    } else {
        let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_2688_);
        crate::leanh::lean_dec_ref(v_m_u2081_2685_);
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
    mut v_00_u03b1_2696_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2697_: *mut crate::leanh::LeanObject,
    mut v_inst_2698_: *mut crate::leanh::LeanObject,
    mut v_inst_2699_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_2700_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(
        v_inst_2698_,
        v_inst_2699_,
        v_m_u2081_2700_,
        v_m_u2082_2701_,
    );
    return v___x_2702_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(
    mut v_inst_2703_: *mut crate::leanh::LeanObject,
    mut v_inst_2704_: *mut crate::leanh::LeanObject,
    mut v_m_2705_: *mut crate::leanh::LeanObject,
    mut v_sofar_2706_: *mut crate::leanh::LeanObject,
    mut v_k_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2704_);
    crate::leanh::lean_inc_ref(v_inst_2703_);
    v___x_2708_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(
        v_inst_2703_,
        v_inst_2704_,
        v_m_2705_,
        v_k_2707_,
    );
    if crate::leanh::lean_obj_tag(v___x_2708_) == 0 {
        crate::leanh::lean_dec_ref(v_inst_2704_);
        crate::leanh::lean_dec_ref(v_inst_2703_);
        return v_sofar_2706_;
    } else {
        let mut v_val_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2709_ = crate::leanh::lean_ctor_get(v___x_2708_, 0);
        crate::leanh::lean_inc(v_val_2709_);
        crate::leanh::lean_dec_ref_known(v___x_2708_, 1);
        v_fst_2710_ = crate::leanh::lean_ctor_get(v_val_2709_, 0);
        crate::leanh::lean_inc(v_fst_2710_);
        v_snd_2711_ = crate::leanh::lean_ctor_get(v_val_2709_, 1);
        crate::leanh::lean_inc(v_snd_2711_);
        crate::leanh::lean_dec(v_val_2709_);
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
    mut v_inst_2713_: *mut crate::leanh::LeanObject,
    mut v_inst_2714_: *mut crate::leanh::LeanObject,
    mut v_m_2715_: *mut crate::leanh::LeanObject,
    mut v_sofar_2716_: *mut crate::leanh::LeanObject,
    mut v_k_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(
        v_inst_2713_,
        v_inst_2714_,
        v_m_2715_,
        v_sofar_2716_,
        v_k_2717_,
    );
    crate::leanh::lean_dec_ref(v_m_2715_);
    return v_res_2718_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(
    mut v_00_u03b1_2719_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2720_: *mut crate::leanh::LeanObject,
    mut v_inst_2721_: *mut crate::leanh::LeanObject,
    mut v_inst_2722_: *mut crate::leanh::LeanObject,
    mut v_m_2723_: *mut crate::leanh::LeanObject,
    mut v_sofar_2724_: *mut crate::leanh::LeanObject,
    mut v_k_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2727_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2728_: *mut crate::leanh::LeanObject,
    mut v_inst_2729_: *mut crate::leanh::LeanObject,
    mut v_inst_2730_: *mut crate::leanh::LeanObject,
    mut v_m_2731_: *mut crate::leanh::LeanObject,
    mut v_sofar_2732_: *mut crate::leanh::LeanObject,
    mut v_k_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(
        v_00_u03b1_2727_,
        v_00_u03b2_2728_,
        v_inst_2729_,
        v_inst_2730_,
        v_m_2731_,
        v_sofar_2732_,
        v_k_2733_,
    );
    crate::leanh::lean_dec_ref(v_m_2731_);
    return v_res_2734_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
    mut v_inst_2735_: *mut crate::leanh::LeanObject,
    mut v_inst_2736_: *mut crate::leanh::LeanObject,
    mut v_m_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2739_ = crate::leanh::lean_ctor_get(v_m_2737_, 1);
    crate::leanh::lean_inc(v_a_2738_);
    v___x_2740_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_2736_, v_buckets_2739_, v_a_2738_);
    v___x_2741_ =
        l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_2735_, v_a_2738_, v___x_2740_);
    return v___x_2741_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(
    mut v_inst_2742_: *mut crate::leanh::LeanObject,
    mut v_inst_2743_: *mut crate::leanh::LeanObject,
    mut v_m_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2742_,
        v_inst_2743_,
        v_m_2744_,
        v_a_2745_,
    );
    crate::leanh::lean_dec_ref(v_m_2744_);
    return v_res_2746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(
    mut v_00_u03b1_2747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2748_: *mut crate::leanh::LeanObject,
    mut v_inst_2749_: *mut crate::leanh::LeanObject,
    mut v_inst_2750_: *mut crate::leanh::LeanObject,
    mut v_m_2751_: *mut crate::leanh::LeanObject,
    mut v_a_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2749_,
        v_inst_2750_,
        v_m_2751_,
        v_a_2752_,
    );
    return v___x_2753_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(
    mut v_00_u03b1_2754_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2755_: *mut crate::leanh::LeanObject,
    mut v_inst_2756_: *mut crate::leanh::LeanObject,
    mut v_inst_2757_: *mut crate::leanh::LeanObject,
    mut v_m_2758_: *mut crate::leanh::LeanObject,
    mut v_a_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(
        v_00_u03b1_2754_,
        v_00_u03b2_2755_,
        v_inst_2756_,
        v_inst_2757_,
        v_m_2758_,
        v_a_2759_,
    );
    crate::leanh::lean_dec_ref(v_m_2758_);
    return v_res_2760_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(
    mut v_inst_2761_: *mut crate::leanh::LeanObject,
    mut v_inst_2762_: *mut crate::leanh::LeanObject,
    mut v_m_2763_: *mut crate::leanh::LeanObject,
    mut v_a_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2765_ = crate::leanh::lean_ctor_get(v_m_2763_, 1);
    crate::leanh::lean_inc(v_a_2764_);
    v___x_2766_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_2762_, v_buckets_2765_, v_a_2764_);
    v___x_2767_ =
        l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_2761_, v_a_2764_, v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(
    mut v_inst_2768_: *mut crate::leanh::LeanObject,
    mut v_inst_2769_: *mut crate::leanh::LeanObject,
    mut v_m_2770_: *mut crate::leanh::LeanObject,
    mut v_a_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(
        v_inst_2768_,
        v_inst_2769_,
        v_m_2770_,
        v_a_2771_,
    );
    crate::leanh::lean_dec_ref(v_m_2770_);
    return v_res_2772_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(
    mut v_00_u03b1_2773_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2774_: *mut crate::leanh::LeanObject,
    mut v_inst_2775_: *mut crate::leanh::LeanObject,
    mut v_inst_2776_: *mut crate::leanh::LeanObject,
    mut v_m_2777_: *mut crate::leanh::LeanObject,
    mut v_a_2778_: *mut crate::leanh::LeanObject,
    mut v_h_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(
        v_inst_2775_,
        v_inst_2776_,
        v_m_2777_,
        v_a_2778_,
    );
    return v___x_2780_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(
    mut v_00_u03b1_2781_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2782_: *mut crate::leanh::LeanObject,
    mut v_inst_2783_: *mut crate::leanh::LeanObject,
    mut v_inst_2784_: *mut crate::leanh::LeanObject,
    mut v_m_2785_: *mut crate::leanh::LeanObject,
    mut v_a_2786_: *mut crate::leanh::LeanObject,
    mut v_h_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(
        v_00_u03b1_2781_,
        v_00_u03b2_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_m_2785_,
        v_a_2786_,
        v_h_2787_,
    );
    crate::leanh::lean_dec_ref(v_m_2785_);
    return v_res_2788_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(
    mut v_inst_2789_: *mut crate::leanh::LeanObject,
    mut v_inst_2790_: *mut crate::leanh::LeanObject,
    mut v_m_2791_: *mut crate::leanh::LeanObject,
    mut v_a_2792_: *mut crate::leanh::LeanObject,
    mut v_fallback_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2789_,
        v_inst_2790_,
        v_m_2791_,
        v_a_2792_,
    );
    if crate::leanh::lean_obj_tag(v___x_2794_) == 0 {
        crate::leanh::lean_inc(v_fallback_2793_);
        return v_fallback_2793_;
    } else {
        let mut v_val_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2795_ = crate::leanh::lean_ctor_get(v___x_2794_, 0);
        crate::leanh::lean_inc(v_val_2795_);
        crate::leanh::lean_dec_ref_known(v___x_2794_, 1);
        return v_val_2795_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(
    mut v_inst_2796_: *mut crate::leanh::LeanObject,
    mut v_inst_2797_: *mut crate::leanh::LeanObject,
    mut v_m_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_fallback_2800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(
        v_inst_2796_,
        v_inst_2797_,
        v_m_2798_,
        v_a_2799_,
        v_fallback_2800_,
    );
    crate::leanh::lean_dec(v_fallback_2800_);
    crate::leanh::lean_dec_ref(v_m_2798_);
    return v_res_2801_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(
    mut v_00_u03b1_2802_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2803_: *mut crate::leanh::LeanObject,
    mut v_inst_2804_: *mut crate::leanh::LeanObject,
    mut v_inst_2805_: *mut crate::leanh::LeanObject,
    mut v_m_2806_: *mut crate::leanh::LeanObject,
    mut v_a_2807_: *mut crate::leanh::LeanObject,
    mut v_fallback_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2810_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2811_: *mut crate::leanh::LeanObject,
    mut v_inst_2812_: *mut crate::leanh::LeanObject,
    mut v_inst_2813_: *mut crate::leanh::LeanObject,
    mut v_m_2814_: *mut crate::leanh::LeanObject,
    mut v_a_2815_: *mut crate::leanh::LeanObject,
    mut v_fallback_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(
        v_00_u03b1_2810_,
        v_00_u03b2_2811_,
        v_inst_2812_,
        v_inst_2813_,
        v_m_2814_,
        v_a_2815_,
        v_fallback_2816_,
    );
    crate::leanh::lean_dec(v_fallback_2816_);
    crate::leanh::lean_dec_ref(v_m_2814_);
    return v_res_2817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(
    mut v_inst_2818_: *mut crate::leanh::LeanObject,
    mut v_inst_2819_: *mut crate::leanh::LeanObject,
    mut v_inst_2820_: *mut crate::leanh::LeanObject,
    mut v_m_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(
        v_inst_2818_,
        v_inst_2819_,
        v_m_2821_,
        v_a_2822_,
    );
    if crate::leanh::lean_obj_tag(v___x_2823_) == 0 {
        let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2824_ = crate::leanh::lean_obj_once(
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
        let mut v_val_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2826_ = crate::leanh::lean_ctor_get(v___x_2823_, 0);
        crate::leanh::lean_inc(v_val_2826_);
        crate::leanh::lean_dec_ref_known(v___x_2823_, 1);
        return v_val_2826_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
    mut v_inst_2828_: *mut crate::leanh::LeanObject,
    mut v_inst_2829_: *mut crate::leanh::LeanObject,
    mut v_m_2830_: *mut crate::leanh::LeanObject,
    mut v_a_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(
        v_inst_2827_,
        v_inst_2828_,
        v_inst_2829_,
        v_m_2830_,
        v_a_2831_,
    );
    crate::leanh::lean_dec_ref(v_m_2830_);
    crate::leanh::lean_dec(v_inst_2829_);
    return v_res_2832_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(
    mut v_00_u03b1_2833_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2834_: *mut crate::leanh::LeanObject,
    mut v_inst_2835_: *mut crate::leanh::LeanObject,
    mut v_inst_2836_: *mut crate::leanh::LeanObject,
    mut v_inst_2837_: *mut crate::leanh::LeanObject,
    mut v_m_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2841_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2842_: *mut crate::leanh::LeanObject,
    mut v_inst_2843_: *mut crate::leanh::LeanObject,
    mut v_inst_2844_: *mut crate::leanh::LeanObject,
    mut v_inst_2845_: *mut crate::leanh::LeanObject,
    mut v_m_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(
        v_00_u03b1_2841_,
        v_00_u03b2_2842_,
        v_inst_2843_,
        v_inst_2844_,
        v_inst_2845_,
        v_m_2846_,
        v_a_2847_,
    );
    crate::leanh::lean_dec_ref(v_m_2846_);
    crate::leanh::lean_dec(v_inst_2845_);
    return v_res_2848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(
    mut v_inst_2849_: *mut crate::leanh::LeanObject,
    mut v_inst_2850_: *mut crate::leanh::LeanObject,
    mut v_m_2851_: *mut crate::leanh::LeanObject,
    mut v_l_2852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_2852_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2850_);
                    crate::leanh::lean_dec_ref(v_inst_2849_);
                    return v_m_2851_;
                } else {
                    v_head_2853_ = crate::leanh::lean_ctor_get(v_l_2852_, 0);
                    crate::leanh::lean_inc(v_head_2853_);
                    v_tail_2854_ = crate::leanh::lean_ctor_get(v_l_2852_, 1);
                    crate::leanh::lean_inc(v_tail_2854_);
                    crate::leanh::lean_dec_ref_known(v_l_2852_, 2);
                    v_fst_2855_ = crate::leanh::lean_ctor_get(v_head_2853_, 0);
                    crate::leanh::lean_inc(v_fst_2855_);
                    v_snd_2856_ = crate::leanh::lean_ctor_get(v_head_2853_, 1);
                    crate::leanh::lean_inc(v_snd_2856_);
                    crate::leanh::lean_dec(v_head_2853_);
                    crate::leanh::lean_inc_ref(v_inst_2850_);
                    crate::leanh::lean_inc_ref(v_inst_2849_);
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
    mut v_00_u03b1_2859_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2860_: *mut crate::leanh::LeanObject,
    mut v_inst_2861_: *mut crate::leanh::LeanObject,
    mut v_inst_2862_: *mut crate::leanh::LeanObject,
    mut v_m_2863_: *mut crate::leanh::LeanObject,
    mut v_l_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(
        v_inst_2861_,
        v_inst_2862_,
        v_m_2863_,
        v_l_2864_,
    );
    return v___x_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(
    mut v_inst_2866_: *mut crate::leanh::LeanObject,
    mut v_inst_2867_: *mut crate::leanh::LeanObject,
    mut v_m_2868_: *mut crate::leanh::LeanObject,
    mut v_l_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_2869_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2867_);
                    crate::leanh::lean_dec_ref(v_inst_2866_);
                    return v_m_2868_;
                } else {
                    v_head_2870_ = crate::leanh::lean_ctor_get(v_l_2869_, 0);
                    crate::leanh::lean_inc(v_head_2870_);
                    v_tail_2871_ = crate::leanh::lean_ctor_get(v_l_2869_, 1);
                    crate::leanh::lean_inc(v_tail_2871_);
                    crate::leanh::lean_dec_ref_known(v_l_2869_, 2);
                    v___x_2872_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_inst_2867_);
                    crate::leanh::lean_inc_ref(v_inst_2866_);
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
    mut v_00_u03b1_2875_: *mut crate::leanh::LeanObject,
    mut v_inst_2876_: *mut crate::leanh::LeanObject,
    mut v_inst_2877_: *mut crate::leanh::LeanObject,
    mut v_m_2878_: *mut crate::leanh::LeanObject,
    mut v_l_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(
        v_inst_2876_,
        v_inst_2877_,
        v_m_2878_,
        v_l_2879_,
    );
    return v___x_2880_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(
    mut v_m_2881_: *mut crate::leanh::LeanObject,
    mut v_h__1_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2883_ = crate::leanh::lean_ctor_get(v_m_2881_, 0);
    crate::leanh::lean_inc(v_size_2883_);
    v_buckets_2884_ = crate::leanh::lean_ctor_get(v_m_2881_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2884_);
    crate::leanh::lean_dec_ref(v_m_2881_);
    v___x_2885_ = crate::leanh::lean_apply_3(
        v_h__1_2882_,
        v_size_2883_,
        v_buckets_2884_,
        crate::leanh::lean_box(0),
    );
    return v___x_2885_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(
    mut v_00_u03b1_2886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2887_: *mut crate::leanh::LeanObject,
    mut v_motive_2888_: *mut crate::leanh::LeanObject,
    mut v_m_2889_: *mut crate::leanh::LeanObject,
    mut v_h__1_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2891_ = crate::leanh::lean_ctor_get(v_m_2889_, 0);
    crate::leanh::lean_inc(v_size_2891_);
    v_buckets_2892_ = crate::leanh::lean_ctor_get(v_m_2889_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2892_);
    crate::leanh::lean_dec_ref(v_m_2889_);
    v___x_2893_ = crate::leanh::lean_apply_3(
        v_h__1_2890_,
        v_size_2891_,
        v_buckets_2892_,
        crate::leanh::lean_box(0),
    );
    return v___x_2893_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___redArg(
    mut v_x_2894_: *mut crate::leanh::LeanObject,
    mut v_h__1_2895_: *mut crate::leanh::LeanObject,
    mut v_h__2_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2894_) == 0 {
        let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2896_);
        v___x_2897_ = crate::leanh::lean_box(0);
        v___x_2898_ = crate::leanh::lean_apply_1(v_h__1_2895_, v___x_2897_);
        return v___x_2898_;
    } else {
        let mut v_val_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2895_);
        v_val_2899_ = crate::leanh::lean_ctor_get(v_x_2894_, 0);
        crate::leanh::lean_inc(v_val_2899_);
        crate::leanh::lean_dec_ref_known(v_x_2894_, 1);
        v___x_2900_ = crate::leanh::lean_apply_1(v_h__2_2896_, v_val_2899_);
        return v___x_2900_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(
    mut v_00_u03b1_2901_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
    mut v_motive_2904_: *mut crate::leanh::LeanObject,
    mut v_x_2905_: *mut crate::leanh::LeanObject,
    mut v_h__1_2906_: *mut crate::leanh::LeanObject,
    mut v_h__2_2907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2905_) == 0 {
        let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2907_);
        v___x_2908_ = crate::leanh::lean_box(0);
        v___x_2909_ = crate::leanh::lean_apply_1(v_h__1_2906_, v___x_2908_);
        return v___x_2909_;
    } else {
        let mut v_val_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2906_);
        v_val_2910_ = crate::leanh::lean_ctor_get(v_x_2905_, 0);
        crate::leanh::lean_inc(v_val_2910_);
        crate::leanh::lean_dec_ref_known(v_x_2905_, 1);
        v___x_2911_ = crate::leanh::lean_apply_1(v_h__2_2907_, v_val_2910_);
        return v___x_2911_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___boxed(
    mut v_00_u03b1_2912_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
    mut v_motive_2915_: *mut crate::leanh::LeanObject,
    mut v_x_2916_: *mut crate::leanh::LeanObject,
    mut v_h__1_2917_: *mut crate::leanh::LeanObject,
    mut v_h__2_2918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2919_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(v_00_u03b1_2912_, v_00_u03b2_2913_, v_a_2914_, v_motive_2915_, v_x_2916_, v_h__1_2917_, v_h__2_2918_);
    crate::leanh::lean_dec(v_a_2914_);
    return v_res_2919_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(
    mut v_x_2920_: *mut crate::leanh::LeanObject,
    mut v_h__1_2921_: *mut crate::leanh::LeanObject,
    mut v_h__2_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2920_) == 0 {
        let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2922_);
        v___x_2923_ = crate::leanh::lean_box(0);
        v___x_2924_ = crate::leanh::lean_apply_1(v_h__1_2921_, v___x_2923_);
        return v___x_2924_;
    } else {
        let mut v_val_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2921_);
        v_val_2925_ = crate::leanh::lean_ctor_get(v_x_2920_, 0);
        crate::leanh::lean_inc(v_val_2925_);
        crate::leanh::lean_dec_ref_known(v_x_2920_, 1);
        v___x_2926_ = crate::leanh::lean_apply_1(v_h__2_2922_, v_val_2925_);
        return v___x_2926_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(
    mut v_00_u03b1_2927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_motive_2930_: *mut crate::leanh::LeanObject,
    mut v_x_2931_: *mut crate::leanh::LeanObject,
    mut v_h__1_2932_: *mut crate::leanh::LeanObject,
    mut v_h__2_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2931_) == 0 {
        let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2933_);
        v___x_2934_ = crate::leanh::lean_box(0);
        v___x_2935_ = crate::leanh::lean_apply_1(v_h__1_2932_, v___x_2934_);
        return v___x_2935_;
    } else {
        let mut v_val_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2932_);
        v_val_2936_ = crate::leanh::lean_ctor_get(v_x_2931_, 0);
        crate::leanh::lean_inc(v_val_2936_);
        crate::leanh::lean_dec_ref_known(v_x_2931_, 1);
        v___x_2937_ = crate::leanh::lean_apply_1(v_h__2_2933_, v_val_2936_);
        return v___x_2937_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_2938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
    mut v_motive_2941_: *mut crate::leanh::LeanObject,
    mut v_x_2942_: *mut crate::leanh::LeanObject,
    mut v_h__1_2943_: *mut crate::leanh::LeanObject,
    mut v_h__2_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_2938_, v_00_u03b2_2939_, v_a_2940_, v_motive_2941_, v_x_2942_, v_h__1_2943_, v_h__2_2944_);
    crate::leanh::lean_dec(v_a_2940_);
    return v_res_2945_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(
    mut v_x_2946_: usize,
    mut v_h__1_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = crate::leanh::lean_box_usize(v_x_2946_);
    v___x_2949_ = crate::leanh::lean_apply_2(v_h__1_2947_, v___x_2948_, crate::leanh::lean_box(0));
    return v___x_2949_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg___boxed(
    mut v_x_2950_: *mut crate::leanh::LeanObject,
    mut v_h__1_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_14__boxed_2952_: usize = 0;
    let mut v_res_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_14__boxed_2952_ = crate::leanh::lean_unbox_usize(v_x_2950_);
    crate::leanh::lean_dec(v_x_2950_);
    v_res_2953_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(v_x_14__boxed_2952_, v_h__1_2951_);
    return v_res_2953_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(
    mut v_00_u03b1_2954_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2955_: *mut crate::leanh::LeanObject,
    mut v_data_2956_: *mut crate::leanh::LeanObject,
    mut v_motive_2957_: *mut crate::leanh::LeanObject,
    mut v_x_2958_: usize,
    mut v_h__1_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = crate::leanh::lean_box_usize(v_x_2958_);
    v___x_2961_ = crate::leanh::lean_apply_2(v_h__1_2959_, v___x_2960_, crate::leanh::lean_box(0));
    return v___x_2961_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___boxed(
    mut v_00_u03b1_2962_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2963_: *mut crate::leanh::LeanObject,
    mut v_data_2964_: *mut crate::leanh::LeanObject,
    mut v_motive_2965_: *mut crate::leanh::LeanObject,
    mut v_x_2966_: *mut crate::leanh::LeanObject,
    mut v_h__1_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_2968_: usize = 0;
    let mut v_res_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_2968_ = crate::leanh::lean_unbox_usize(v_x_2966_);
    crate::leanh::lean_dec(v_x_2966_);
    v_res_2969_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(v_00_u03b1_2962_, v_00_u03b2_2963_, v_data_2964_, v_motive_2965_, v_x_21__boxed_2968_, v_h__1_2967_);
    crate::leanh::lean_dec_ref(v_data_2964_);
    return v_res_2969_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter___redArg(
    mut v_m_2970_: *mut crate::leanh::LeanObject,
    mut v_h__1_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2972_ = crate::leanh::lean_ctor_get(v_m_2970_, 0);
    crate::leanh::lean_inc(v_size_2972_);
    v_buckets_2973_ = crate::leanh::lean_ctor_get(v_m_2970_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2973_);
    crate::leanh::lean_dec_ref(v_m_2970_);
    v___x_2974_ = crate::leanh::lean_apply_3(
        v_h__1_2971_,
        v_size_2972_,
        v_buckets_2973_,
        crate::leanh::lean_box(0),
    );
    return v___x_2974_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter(
    mut v_00_u03b1_2975_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2976_: *mut crate::leanh::LeanObject,
    mut v_motive_2977_: *mut crate::leanh::LeanObject,
    mut v_m_2978_: *mut crate::leanh::LeanObject,
    mut v_h__1_2979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_2980_ = crate::leanh::lean_ctor_get(v_m_2978_, 0);
    crate::leanh::lean_inc(v_size_2980_);
    v_buckets_2981_ = crate::leanh::lean_ctor_get(v_m_2978_, 1);
    crate::leanh::lean_inc_ref(v_buckets_2981_);
    crate::leanh::lean_dec_ref(v_m_2978_);
    v___x_2982_ = crate::leanh::lean_apply_3(
        v_h__1_2979_,
        v_size_2980_,
        v_buckets_2981_,
        crate::leanh::lean_box(0),
    );
    return v___x_2982_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(
    mut v_x_2983_: *mut crate::leanh::LeanObject,
    mut v_h__1_2984_: *mut crate::leanh::LeanObject,
    mut v_h__2_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2983_) == 0 {
        let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2985_);
        v___x_2986_ = crate::leanh::lean_box(0);
        v___x_2987_ = crate::leanh::lean_apply_1(v_h__1_2984_, v___x_2986_);
        return v___x_2987_;
    } else {
        let mut v_val_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2984_);
        v_val_2988_ = crate::leanh::lean_ctor_get(v_x_2983_, 0);
        crate::leanh::lean_inc(v_val_2988_);
        crate::leanh::lean_dec_ref_known(v_x_2983_, 1);
        v___x_2989_ = crate::leanh::lean_apply_1(v_h__2_2985_, v_val_2988_);
        return v___x_2989_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(
    mut v_00_u03b2_2990_: *mut crate::leanh::LeanObject,
    mut v_motive_2991_: *mut crate::leanh::LeanObject,
    mut v_x_2992_: *mut crate::leanh::LeanObject,
    mut v_h__1_2993_: *mut crate::leanh::LeanObject,
    mut v_h__2_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2992_) == 0 {
        let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2994_);
        v___x_2995_ = crate::leanh::lean_box(0);
        v___x_2996_ = crate::leanh::lean_apply_1(v_h__1_2993_, v___x_2995_);
        return v___x_2996_;
    } else {
        let mut v_val_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2993_);
        v_val_2997_ = crate::leanh::lean_ctor_get(v_x_2992_, 0);
        crate::leanh::lean_inc(v_val_2997_);
        crate::leanh::lean_dec_ref_known(v_x_2992_, 1);
        v___x_2998_ = crate::leanh::lean_apply_1(v_h__2_2994_, v_val_2997_);
        return v___x_2998_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(
    mut v_x_2999_: *mut crate::leanh::LeanObject,
    mut v_h__1_3000_: *mut crate::leanh::LeanObject,
    mut v_h__2_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2999_) == 0 {
        let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3001_);
        v___x_3002_ = crate::leanh::lean_box(0);
        v___x_3003_ = crate::leanh::lean_apply_1(v_h__1_3000_, v___x_3002_);
        return v___x_3003_;
    } else {
        let mut v_val_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3000_);
        v_val_3004_ = crate::leanh::lean_ctor_get(v_x_2999_, 0);
        crate::leanh::lean_inc(v_val_3004_);
        crate::leanh::lean_dec_ref_known(v_x_2999_, 1);
        v___x_3005_ = crate::leanh::lean_apply_1(v_h__2_3001_, v_val_3004_);
        return v___x_3005_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(
    mut v_00_u03b2_3006_: *mut crate::leanh::LeanObject,
    mut v_motive_3007_: *mut crate::leanh::LeanObject,
    mut v_x_3008_: *mut crate::leanh::LeanObject,
    mut v_h__1_3009_: *mut crate::leanh::LeanObject,
    mut v_h__2_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3008_) == 0 {
        let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3010_);
        v___x_3011_ = crate::leanh::lean_box(0);
        v___x_3012_ = crate::leanh::lean_apply_1(v_h__1_3009_, v___x_3011_);
        return v___x_3012_;
    } else {
        let mut v_val_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3009_);
        v_val_3013_ = crate::leanh::lean_ctor_get(v_x_3008_, 0);
        crate::leanh::lean_inc(v_val_3013_);
        crate::leanh::lean_dec_ref_known(v_x_3008_, 1);
        v___x_3014_ = crate::leanh::lean_apply_1(v_h__2_3010_, v_val_3013_);
        return v___x_3014_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(
    mut v_x_3015_: usize,
    mut v_h__1_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = crate::leanh::lean_box_usize(v_x_3015_);
    v___x_3018_ = crate::leanh::lean_apply_2(v_h__1_3016_, v___x_3017_, crate::leanh::lean_box(0));
    return v___x_3018_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(
    mut v_x_3019_: *mut crate::leanh::LeanObject,
    mut v_h__1_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_14__boxed_3021_: usize = 0;
    let mut v_res_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_14__boxed_3021_ = crate::leanh::lean_unbox_usize(v_x_3019_);
    crate::leanh::lean_dec(v_x_3019_);
    v_res_3022_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(v_x_14__boxed_3021_, v_h__1_3020_);
    return v_res_3022_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(
    mut v_00_u03b1_3023_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3024_: *mut crate::leanh::LeanObject,
    mut v_buckets_3025_: *mut crate::leanh::LeanObject,
    mut v_motive_3026_: *mut crate::leanh::LeanObject,
    mut v_x_3027_: usize,
    mut v_h__1_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = crate::leanh::lean_box_usize(v_x_3027_);
    v___x_3030_ = crate::leanh::lean_apply_2(v_h__1_3028_, v___x_3029_, crate::leanh::lean_box(0));
    return v___x_3030_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(
    mut v_00_u03b1_3031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3032_: *mut crate::leanh::LeanObject,
    mut v_buckets_3033_: *mut crate::leanh::LeanObject,
    mut v_motive_3034_: *mut crate::leanh::LeanObject,
    mut v_x_3035_: *mut crate::leanh::LeanObject,
    mut v_h__1_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_3037_: usize = 0;
    let mut v_res_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_3037_ = crate::leanh::lean_unbox_usize(v_x_3035_);
    crate::leanh::lean_dec(v_x_3035_);
    v_res_3038_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(v_00_u03b1_3031_, v_00_u03b2_3032_, v_buckets_3033_, v_motive_3034_, v_x_21__boxed_3037_, v_h__1_3036_);
    crate::leanh::lean_dec_ref(v_buckets_3033_);
    return v_res_3038_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(
    mut v_l_3039_: *mut crate::leanh::LeanObject,
    mut v_h__1_3040_: *mut crate::leanh::LeanObject,
    mut v_h__2_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3039_) == 0 {
        let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3041_);
        v___x_3042_ = crate::leanh::lean_box(0);
        v___x_3043_ = crate::leanh::lean_apply_1(v_h__1_3040_, v___x_3042_);
        return v___x_3043_;
    } else {
        let mut v_head_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3040_);
        v_head_3044_ = crate::leanh::lean_ctor_get(v_l_3039_, 0);
        crate::leanh::lean_inc(v_head_3044_);
        v_tail_3045_ = crate::leanh::lean_ctor_get(v_l_3039_, 1);
        crate::leanh::lean_inc(v_tail_3045_);
        crate::leanh::lean_dec_ref_known(v_l_3039_, 2);
        v___x_3046_ = crate::leanh::lean_apply_2(v_h__2_3041_, v_head_3044_, v_tail_3045_);
        return v___x_3046_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(
    mut v_00_u03b1_3047_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3048_: *mut crate::leanh::LeanObject,
    mut v_motive_3049_: *mut crate::leanh::LeanObject,
    mut v_l_3050_: *mut crate::leanh::LeanObject,
    mut v_h__1_3051_: *mut crate::leanh::LeanObject,
    mut v_h__2_3052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3050_) == 0 {
        let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3052_);
        v___x_3053_ = crate::leanh::lean_box(0);
        v___x_3054_ = crate::leanh::lean_apply_1(v_h__1_3051_, v___x_3053_);
        return v___x_3054_;
    } else {
        let mut v_head_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3051_);
        v_head_3055_ = crate::leanh::lean_ctor_get(v_l_3050_, 0);
        crate::leanh::lean_inc(v_head_3055_);
        v_tail_3056_ = crate::leanh::lean_ctor_get(v_l_3050_, 1);
        crate::leanh::lean_inc(v_tail_3056_);
        crate::leanh::lean_dec_ref_known(v_l_3050_, 2);
        v___x_3057_ = crate::leanh::lean_apply_2(v_h__2_3052_, v_head_3055_, v_tail_3056_);
        return v___x_3057_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(
    mut v_l_3058_: *mut crate::leanh::LeanObject,
    mut v_h__1_3059_: *mut crate::leanh::LeanObject,
    mut v_h__2_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3058_) == 0 {
        let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3060_);
        v___x_3061_ = crate::leanh::lean_box(0);
        v___x_3062_ = crate::leanh::lean_apply_1(v_h__1_3059_, v___x_3061_);
        return v___x_3062_;
    } else {
        let mut v_head_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3059_);
        v_head_3063_ = crate::leanh::lean_ctor_get(v_l_3058_, 0);
        crate::leanh::lean_inc(v_head_3063_);
        v_tail_3064_ = crate::leanh::lean_ctor_get(v_l_3058_, 1);
        crate::leanh::lean_inc(v_tail_3064_);
        crate::leanh::lean_dec_ref_known(v_l_3058_, 2);
        v___x_3065_ = crate::leanh::lean_apply_2(v_h__2_3060_, v_head_3063_, v_tail_3064_);
        return v___x_3065_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(
    mut v_00_u03b1_3066_: *mut crate::leanh::LeanObject,
    mut v_motive_3067_: *mut crate::leanh::LeanObject,
    mut v_l_3068_: *mut crate::leanh::LeanObject,
    mut v_h__1_3069_: *mut crate::leanh::LeanObject,
    mut v_h__2_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3068_) == 0 {
        let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3070_);
        v___x_3071_ = crate::leanh::lean_box(0);
        v___x_3072_ = crate::leanh::lean_apply_1(v_h__1_3069_, v___x_3071_);
        return v___x_3072_;
    } else {
        let mut v_head_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3069_);
        v_head_3073_ = crate::leanh::lean_ctor_get(v_l_3068_, 0);
        crate::leanh::lean_inc(v_head_3073_);
        v_tail_3074_ = crate::leanh::lean_ctor_get(v_l_3068_, 1);
        crate::leanh::lean_inc(v_tail_3074_);
        crate::leanh::lean_dec_ref_known(v_l_3068_, 2);
        v___x_3075_ = crate::leanh::lean_apply_2(v_h__2_3070_, v_head_3073_, v_tail_3074_);
        return v___x_3075_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(
    mut v_l_3076_: *mut crate::leanh::LeanObject,
    mut v_h__1_3077_: *mut crate::leanh::LeanObject,
    mut v_h__2_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3076_) == 0 {
        let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3078_);
        v___x_3079_ = crate::leanh::lean_box(0);
        v___x_3080_ = crate::leanh::lean_apply_1(v_h__1_3077_, v___x_3079_);
        return v___x_3080_;
    } else {
        let mut v_head_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3077_);
        v_head_3081_ = crate::leanh::lean_ctor_get(v_l_3076_, 0);
        crate::leanh::lean_inc(v_head_3081_);
        v_tail_3082_ = crate::leanh::lean_ctor_get(v_l_3076_, 1);
        crate::leanh::lean_inc(v_tail_3082_);
        crate::leanh::lean_dec_ref_known(v_l_3076_, 2);
        v___x_3083_ = crate::leanh::lean_apply_2(v_h__2_3078_, v_head_3081_, v_tail_3082_);
        return v___x_3083_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(
    mut v_00_u03b1_3084_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3085_: *mut crate::leanh::LeanObject,
    mut v_motive_3086_: *mut crate::leanh::LeanObject,
    mut v_l_3087_: *mut crate::leanh::LeanObject,
    mut v_h__1_3088_: *mut crate::leanh::LeanObject,
    mut v_h__2_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_3087_) == 0 {
        let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3089_);
        v___x_3090_ = crate::leanh::lean_box(0);
        v___x_3091_ = crate::leanh::lean_apply_1(v_h__1_3088_, v___x_3090_);
        return v___x_3091_;
    } else {
        let mut v_head_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3088_);
        v_head_3092_ = crate::leanh::lean_ctor_get(v_l_3087_, 0);
        crate::leanh::lean_inc(v_head_3092_);
        v_tail_3093_ = crate::leanh::lean_ctor_get(v_l_3087_, 1);
        crate::leanh::lean_inc(v_tail_3093_);
        crate::leanh::lean_dec_ref_known(v_l_3087_, 2);
        v___x_3094_ = crate::leanh::lean_apply_2(v_h__2_3089_, v_head_3092_, v_tail_3093_);
        return v___x_3094_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_Model(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_Model(builtin);
}
