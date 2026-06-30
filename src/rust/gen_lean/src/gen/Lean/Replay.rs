// Lean compiler output
// Module: Lean.Replay
// Imports: Lean.CoreM Lean.AddDecl Lean.Util.FoldConsts
use crate::ffi::{
    lean_add_decl, lean_array_get_size, lean_array_uget_borrowed, lean_expr_eqv, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_nat_mul, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_dec_eq,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::{initialize_Lean_AddDecl, runtime_initialize_Lean_AddDecl};
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_inductiveVal_x21, l_Lean_ConstantInfo_isPartial,
    l_Lean_ConstantInfo_isUnsafe, l_Lean_ConstantInfo_name, l_Lean_ConstantInfo_type,
    l_Lean_instBEqConstructorVal_beq, l_Lean_instBEqRecursorVal_beq,
    l_Lean_instInhabitedConstantInfo_default,
};
use crate::r#gen::Lean::Environment::{
    lean_elab_environment_of_kernel_env, lean_elab_environment_to_kernel_env, lean_environment_find,
};
use crate::r#gen::Lean::Message::{
    l_Lean_Kernel_Exception_toMessageData, l_Lean_MessageData_toString,
};
use crate::r#gen::Lean::Util::FoldConsts::{
    initialize_Lean_Util_FoldConsts, l_Lean_ConstantInfo_getUsedConstantsAsSet,
    runtime_initialize_Lean_Util_FoldConsts,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
static mut l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0: u64 = 0;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__0_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        119, 104, 105, 108, 101, 32, 114, 101, 112, 108, 97, 121, 105, 110, 103, 32, 100, 101, 99,
        108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [39, 58, 10, 0],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__5_value:
    leanh::LeanStringObject<62> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 82, 101, 112, 108, 97, 121,
        46, 48, 46, 76, 101, 97, 110, 46, 69, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 46,
        82, 101, 112, 108, 97, 121, 46, 114, 101, 112, 108, 97, 121, 67, 111, 110, 115, 116, 97,
        110, 116, 0,
    ],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__4_value:
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
    m_data: [76, 101, 97, 110, 46, 82, 101, 112, 108, 97, 121, 0],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [78, 111, 32, 115, 117, 99, 104, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [78, 111, 32, 115, 117, 99, 104, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(
    mut v_k_1755_: *mut leanh::LeanObject,
    mut v_t_1756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v_impl_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v_size_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v_unused_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_unused_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v_size_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_unused_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v_k_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v_size_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_unused_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_unused_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v_k_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_unused_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_unused_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v_size_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_unused_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_unused_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v_k_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut v_unused_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v_k_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_unused_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut v_unused_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_unused_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v_size_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2306_: u8 = 0;
    let mut v_unused_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2320_: u8 = 0;
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut v_unused_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v_size_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_unused_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_unused_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v_k_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v_unused_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_unused_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_unused_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1756_) == 0 {
                    v_k_1757_ = leanh::lean_ctor_get(v_t_1756_, 1);
                    v_v_1758_ = leanh::lean_ctor_get(v_t_1756_, 2);
                    v_l_1759_ = leanh::lean_ctor_get(v_t_1756_, 3);
                    v_r_1760_ = leanh::lean_ctor_get(v_t_1756_, 4);
                    v_isSharedCheck_2414_ = (!leanh::lean_is_exclusive(v_t_1756_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v_unused_2415_ = leanh::lean_ctor_get(v_t_1756_, 0);
                        leanh::lean_dec(v_unused_2415_);
                        v___x_1762_ = v_t_1756_;
                        v_isShared_1763_ = v_isSharedCheck_2414_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1760_);
                        leanh::lean_inc(v_l_1759_);
                        leanh::lean_inc(v_v_1758_);
                        leanh::lean_inc(v_k_1757_);
                        leanh::lean_dec(v_t_1756_);
                        v___x_1762_ = leanh::lean_box(0);
                        v_isShared_1763_ = v_isSharedCheck_2414_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1756_;
                }
            }
            1 => {
                v___x_1764_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1755_, v_k_1757_);
                match v___x_1764_ {
                    0 => {
                        v_impl_1765_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_k_1755_, v_l_1759_);
                        v___x_1766_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_1765_) == 0 {
                            if leanh::lean_obj_tag(v_r_1760_) == 0 {
                                v_size_1767_ = leanh::lean_ctor_get(v_impl_1765_, 0);
                                leanh::lean_inc(v_size_1767_);
                                v_size_1768_ = leanh::lean_ctor_get(v_r_1760_, 0);
                                v_k_1769_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                v_v_1770_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                v_l_1771_ = leanh::lean_ctor_get(v_r_1760_, 3);
                                leanh::lean_inc(v_l_1771_);
                                v_r_1772_ = leanh::lean_ctor_get(v_r_1760_, 4);
                                v___x_1773_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1774_ = lean_nat_mul(v___x_1773_, v_size_1767_);
                                v___x_1775_ = lean_nat_dec_lt(v___x_1774_, v_size_1768_);
                                leanh::lean_dec(v___x_1774_);
                                if v___x_1775_ == 0 {
                                    leanh::lean_dec(v_l_1771_);
                                    v___x_1776_ = lean_nat_add(v___x_1766_, v_size_1767_);
                                    leanh::lean_dec(v_size_1767_);
                                    v___x_1777_ = lean_nat_add(v___x_1776_, v_size_1768_);
                                    leanh::lean_dec(v___x_1776_);
                                    if v_isShared_1763_ == 0 {
                                        leanh::lean_ctor_set(v___x_1762_, 3, v_impl_1765_);
                                        leanh::lean_ctor_set(v___x_1762_, 0, v___x_1777_);
                                        v___x_1779_ = v___x_1762_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1780_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1780_,
                                            0,
                                            v___x_1777_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1780_,
                                            1,
                                            v_k_1757_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1780_,
                                            2,
                                            v_v_1758_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1780_,
                                            3,
                                            v_impl_1765_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1780_,
                                            4,
                                            v_r_1760_,
                                        );
                                        v___x_1779_ = v_reuseFailAlloc_1780_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_1772_);
                                    leanh::lean_inc(v_v_1770_);
                                    leanh::lean_inc(v_k_1769_);
                                    leanh::lean_inc(v_size_1768_);
                                    v_isSharedCheck_1844_ =
                                        (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v_unused_1845_ = leanh::lean_ctor_get(v_r_1760_, 4);
                                        leanh::lean_dec(v_unused_1845_);
                                        v_unused_1846_ = leanh::lean_ctor_get(v_r_1760_, 3);
                                        leanh::lean_dec(v_unused_1846_);
                                        v_unused_1847_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                        leanh::lean_dec(v_unused_1847_);
                                        v_unused_1848_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                        leanh::lean_dec(v_unused_1848_);
                                        v_unused_1849_ = leanh::lean_ctor_get(v_r_1760_, 0);
                                        leanh::lean_dec(v_unused_1849_);
                                        v___x_1782_ = v_r_1760_;
                                        v_isShared_1783_ = v_isSharedCheck_1844_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_1760_);
                                        v___x_1782_ = leanh::lean_box(0);
                                        v_isShared_1783_ = v_isSharedCheck_1844_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1850_ = leanh::lean_ctor_get(v_impl_1765_, 0);
                                leanh::lean_inc(v_size_1850_);
                                v___x_1851_ = lean_nat_add(v___x_1766_, v_size_1850_);
                                leanh::lean_dec(v_size_1850_);
                                if v_isShared_1763_ == 0 {
                                    leanh::lean_ctor_set(v___x_1762_, 3, v_impl_1765_);
                                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1851_);
                                    v___x_1853_ = v___x_1762_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1854_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1854_,
                                        0,
                                        v___x_1851_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1854_,
                                        1,
                                        v_k_1757_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1854_,
                                        2,
                                        v_v_1758_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1854_,
                                        3,
                                        v_impl_1765_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1854_,
                                        4,
                                        v_r_1760_,
                                    );
                                    v___x_1853_ = v_reuseFailAlloc_1854_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_r_1760_) == 0 {
                                v_l_1855_ = leanh::lean_ctor_get(v_r_1760_, 3);
                                leanh::lean_inc(v_l_1855_);
                                if leanh::lean_obj_tag(v_l_1855_) == 0 {
                                    v_r_1856_ = leanh::lean_ctor_get(v_r_1760_, 4);
                                    leanh::lean_inc(v_r_1856_);
                                    if leanh::lean_obj_tag(v_r_1856_) == 0 {
                                        v_size_1857_ = leanh::lean_ctor_get(v_r_1760_, 0);
                                        v_k_1858_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                        v_v_1859_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1872_ =
                                            (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1872_ == 0 {
                                            v_unused_1873_ =
                                                leanh::lean_ctor_get(v_r_1760_, 4);
                                            leanh::lean_dec(v_unused_1873_);
                                            v_unused_1874_ =
                                                leanh::lean_ctor_get(v_r_1760_, 3);
                                            leanh::lean_dec(v_unused_1874_);
                                            v___x_1861_ = v_r_1760_;
                                            v_isShared_1862_ = v_isSharedCheck_1872_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1859_);
                                            leanh::lean_inc(v_k_1858_);
                                            leanh::lean_inc(v_size_1857_);
                                            leanh::lean_dec(v_r_1760_);
                                            v___x_1861_ = leanh::lean_box(0);
                                            v_isShared_1862_ = v_isSharedCheck_1872_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1875_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                        v_v_1876_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1899_ =
                                            (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1899_ == 0 {
                                            v_unused_1900_ =
                                                leanh::lean_ctor_get(v_r_1760_, 4);
                                            leanh::lean_dec(v_unused_1900_);
                                            v_unused_1901_ =
                                                leanh::lean_ctor_get(v_r_1760_, 3);
                                            leanh::lean_dec(v_unused_1901_);
                                            v_unused_1902_ =
                                                leanh::lean_ctor_get(v_r_1760_, 0);
                                            leanh::lean_dec(v_unused_1902_);
                                            v___x_1878_ = v_r_1760_;
                                            v_isShared_1879_ = v_isSharedCheck_1899_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1876_);
                                            leanh::lean_inc(v_k_1875_);
                                            leanh::lean_dec(v_r_1760_);
                                            v___x_1878_ = leanh::lean_box(0);
                                            v_isShared_1879_ = v_isSharedCheck_1899_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1903_ = leanh::lean_ctor_get(v_r_1760_, 4);
                                    leanh::lean_inc(v_r_1903_);
                                    if leanh::lean_obj_tag(v_r_1903_) == 0 {
                                        v_k_1904_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                        v_v_1905_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1916_ =
                                            (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1916_ == 0 {
                                            v_unused_1917_ =
                                                leanh::lean_ctor_get(v_r_1760_, 4);
                                            leanh::lean_dec(v_unused_1917_);
                                            v_unused_1918_ =
                                                leanh::lean_ctor_get(v_r_1760_, 3);
                                            leanh::lean_dec(v_unused_1918_);
                                            v_unused_1919_ =
                                                leanh::lean_ctor_get(v_r_1760_, 0);
                                            leanh::lean_dec(v_unused_1919_);
                                            v___x_1907_ = v_r_1760_;
                                            v_isShared_1908_ = v_isSharedCheck_1916_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1905_);
                                            leanh::lean_inc(v_k_1904_);
                                            leanh::lean_dec(v_r_1760_);
                                            v___x_1907_ = leanh::lean_box(0);
                                            v_isShared_1908_ = v_isSharedCheck_1916_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_1920_ = leanh::lean_ctor_get(v_r_1760_, 0);
                                        v_k_1921_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                        v_v_1922_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1933_ =
                                            (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1933_ == 0 {
                                            v_unused_1934_ =
                                                leanh::lean_ctor_get(v_r_1760_, 4);
                                            leanh::lean_dec(v_unused_1934_);
                                            v_unused_1935_ =
                                                leanh::lean_ctor_get(v_r_1760_, 3);
                                            leanh::lean_dec(v_unused_1935_);
                                            v___x_1924_ = v_r_1760_;
                                            v_isShared_1925_ = v_isSharedCheck_1933_;
                                            state = 25;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1922_);
                                            leanh::lean_inc(v_k_1921_);
                                            leanh::lean_inc(v_size_1920_);
                                            leanh::lean_dec(v_r_1760_);
                                            v___x_1924_ = leanh::lean_box(0);
                                            v_isShared_1925_ = v_isSharedCheck_1933_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_1763_ == 0 {
                                    leanh::lean_ctor_set(v___x_1762_, 3, v_r_1760_);
                                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1766_);
                                    v___x_1937_ = v___x_1762_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1938_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1938_,
                                        0,
                                        v___x_1766_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1938_,
                                        1,
                                        v_k_1757_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1938_,
                                        2,
                                        v_v_1758_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1938_,
                                        3,
                                        v_r_1760_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1938_,
                                        4,
                                        v_r_1760_,
                                    );
                                    v___x_1937_ = v_reuseFailAlloc_1938_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_1762_);
                        leanh::lean_dec(v_v_1758_);
                        leanh::lean_dec(v_k_1757_);
                        if leanh::lean_obj_tag(v_l_1759_) == 0 {
                            if leanh::lean_obj_tag(v_r_1760_) == 0 {
                                v_size_1939_ = leanh::lean_ctor_get(v_l_1759_, 0);
                                v_k_1940_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                v_v_1941_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                v_l_1942_ = leanh::lean_ctor_get(v_l_1759_, 3);
                                v_r_1943_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                leanh::lean_inc(v_r_1943_);
                                v_size_1944_ = leanh::lean_ctor_get(v_r_1760_, 0);
                                v_k_1945_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                v_v_1946_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                v_l_1947_ = leanh::lean_ctor_get(v_r_1760_, 3);
                                leanh::lean_inc(v_l_1947_);
                                v_r_1948_ = leanh::lean_ctor_get(v_r_1760_, 4);
                                v___x_1949_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1950_ = lean_nat_dec_lt(v_size_1939_, v_size_1944_);
                                if v___x_1950_ == 0 {
                                    leanh::lean_inc(v_l_1942_);
                                    leanh::lean_inc(v_v_1941_);
                                    leanh::lean_inc(v_k_1940_);
                                    v_isSharedCheck_2086_ =
                                        (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                                    if v_isSharedCheck_2086_ == 0 {
                                        v_unused_2087_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                        leanh::lean_dec(v_unused_2087_);
                                        v_unused_2088_ = leanh::lean_ctor_get(v_l_1759_, 3);
                                        leanh::lean_dec(v_unused_2088_);
                                        v_unused_2089_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                        leanh::lean_dec(v_unused_2089_);
                                        v_unused_2090_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                        leanh::lean_dec(v_unused_2090_);
                                        v_unused_2091_ = leanh::lean_ctor_get(v_l_1759_, 0);
                                        leanh::lean_dec(v_unused_2091_);
                                        v___x_1952_ = v_l_1759_;
                                        v_isShared_1953_ = v_isSharedCheck_2086_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_1759_);
                                        v___x_1952_ = leanh::lean_box(0);
                                        v_isShared_1953_ = v_isSharedCheck_2086_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_1948_);
                                    leanh::lean_inc(v_v_1946_);
                                    leanh::lean_inc(v_k_1945_);
                                    v_isSharedCheck_2244_ =
                                        (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                                    if v_isSharedCheck_2244_ == 0 {
                                        v_unused_2245_ = leanh::lean_ctor_get(v_r_1760_, 4);
                                        leanh::lean_dec(v_unused_2245_);
                                        v_unused_2246_ = leanh::lean_ctor_get(v_r_1760_, 3);
                                        leanh::lean_dec(v_unused_2246_);
                                        v_unused_2247_ = leanh::lean_ctor_get(v_r_1760_, 2);
                                        leanh::lean_dec(v_unused_2247_);
                                        v_unused_2248_ = leanh::lean_ctor_get(v_r_1760_, 1);
                                        leanh::lean_dec(v_unused_2248_);
                                        v_unused_2249_ = leanh::lean_ctor_get(v_r_1760_, 0);
                                        leanh::lean_dec(v_unused_2249_);
                                        v___x_2093_ = v_r_1760_;
                                        v_isShared_2094_ = v_isSharedCheck_2244_;
                                        state = 51;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_1760_);
                                        v___x_2093_ = leanh::lean_box(0);
                                        v_isShared_2094_ = v_isSharedCheck_2244_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_1759_;
                            }
                        } else {
                            return v_r_1760_;
                        }
                    }
                    _ => {
                        v_impl_2250_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_k_1755_, v_r_1760_);
                        v___x_2251_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_2250_) == 0 {
                            if leanh::lean_obj_tag(v_l_1759_) == 0 {
                                v_size_2252_ = leanh::lean_ctor_get(v_impl_2250_, 0);
                                leanh::lean_inc(v_size_2252_);
                                v_size_2253_ = leanh::lean_ctor_get(v_l_1759_, 0);
                                v_k_2254_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                v_v_2255_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                v_l_2256_ = leanh::lean_ctor_get(v_l_1759_, 3);
                                v_r_2257_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                leanh::lean_inc(v_r_2257_);
                                v___x_2258_ = leanh::lean_unsigned_to_nat(3);
                                v___x_2259_ = lean_nat_mul(v___x_2258_, v_size_2252_);
                                v___x_2260_ = lean_nat_dec_lt(v___x_2259_, v_size_2253_);
                                leanh::lean_dec(v___x_2259_);
                                if v___x_2260_ == 0 {
                                    leanh::lean_dec(v_r_2257_);
                                    v___x_2261_ = lean_nat_add(v___x_2251_, v_size_2253_);
                                    v___x_2262_ = lean_nat_add(v___x_2261_, v_size_2252_);
                                    leanh::lean_dec(v_size_2252_);
                                    leanh::lean_dec(v___x_2261_);
                                    if v_isShared_1763_ == 0 {
                                        leanh::lean_ctor_set(v___x_1762_, 4, v_impl_2250_);
                                        leanh::lean_ctor_set(v___x_1762_, 0, v___x_2262_);
                                        v___x_2264_ = v___x_1762_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2265_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2265_,
                                            0,
                                            v___x_2262_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2265_,
                                            1,
                                            v_k_1757_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2265_,
                                            2,
                                            v_v_1758_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2265_,
                                            3,
                                            v_l_1759_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2265_,
                                            4,
                                            v_impl_2250_,
                                        );
                                        v___x_2264_ = v_reuseFailAlloc_2265_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_l_2256_);
                                    leanh::lean_inc(v_v_2255_);
                                    leanh::lean_inc(v_k_2254_);
                                    leanh::lean_inc(v_size_2253_);
                                    v_isSharedCheck_2331_ =
                                        (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                                    if v_isSharedCheck_2331_ == 0 {
                                        v_unused_2332_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                        leanh::lean_dec(v_unused_2332_);
                                        v_unused_2333_ = leanh::lean_ctor_get(v_l_1759_, 3);
                                        leanh::lean_dec(v_unused_2333_);
                                        v_unused_2334_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                        leanh::lean_dec(v_unused_2334_);
                                        v_unused_2335_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                        leanh::lean_dec(v_unused_2335_);
                                        v_unused_2336_ = leanh::lean_ctor_get(v_l_1759_, 0);
                                        leanh::lean_dec(v_unused_2336_);
                                        v___x_2267_ = v_l_1759_;
                                        v_isShared_2268_ = v_isSharedCheck_2331_;
                                        state = 75;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_1759_);
                                        v___x_2267_ = leanh::lean_box(0);
                                        v_isShared_2268_ = v_isSharedCheck_2331_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2337_ = leanh::lean_ctor_get(v_impl_2250_, 0);
                                leanh::lean_inc(v_size_2337_);
                                v___x_2338_ = lean_nat_add(v___x_2251_, v_size_2337_);
                                leanh::lean_dec(v_size_2337_);
                                if v_isShared_1763_ == 0 {
                                    leanh::lean_ctor_set(v___x_1762_, 4, v_impl_2250_);
                                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_2338_);
                                    v___x_2340_ = v___x_1762_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2341_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2341_,
                                        0,
                                        v___x_2338_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2341_,
                                        1,
                                        v_k_1757_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2341_,
                                        2,
                                        v_v_1758_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2341_,
                                        3,
                                        v_l_1759_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2341_,
                                        4,
                                        v_impl_2250_,
                                    );
                                    v___x_2340_ = v_reuseFailAlloc_2341_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_l_1759_) == 0 {
                                v_l_2342_ = leanh::lean_ctor_get(v_l_1759_, 3);
                                if leanh::lean_obj_tag(v_l_2342_) == 0 {
                                    leanh::lean_inc_ref(v_l_2342_);
                                    v_r_2343_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                    leanh::lean_inc(v_r_2343_);
                                    if leanh::lean_obj_tag(v_r_2343_) == 0 {
                                        v_size_2344_ = leanh::lean_ctor_get(v_l_1759_, 0);
                                        v_k_2345_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                        v_v_2346_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                        v_isSharedCheck_2359_ =
                                            (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                                        if v_isSharedCheck_2359_ == 0 {
                                            v_unused_2360_ =
                                                leanh::lean_ctor_get(v_l_1759_, 4);
                                            leanh::lean_dec(v_unused_2360_);
                                            v_unused_2361_ =
                                                leanh::lean_ctor_get(v_l_1759_, 3);
                                            leanh::lean_dec(v_unused_2361_);
                                            v___x_2348_ = v_l_1759_;
                                            v_isShared_2349_ = v_isSharedCheck_2359_;
                                            state = 86;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2346_);
                                            leanh::lean_inc(v_k_2345_);
                                            leanh::lean_inc(v_size_2344_);
                                            leanh::lean_dec(v_l_1759_);
                                            v___x_2348_ = leanh::lean_box(0);
                                            v_isShared_2349_ = v_isSharedCheck_2359_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_2362_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                        v_v_2363_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                        v_isSharedCheck_2374_ =
                                            (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                                        if v_isSharedCheck_2374_ == 0 {
                                            v_unused_2375_ =
                                                leanh::lean_ctor_get(v_l_1759_, 4);
                                            leanh::lean_dec(v_unused_2375_);
                                            v_unused_2376_ =
                                                leanh::lean_ctor_get(v_l_1759_, 3);
                                            leanh::lean_dec(v_unused_2376_);
                                            v_unused_2377_ =
                                                leanh::lean_ctor_get(v_l_1759_, 0);
                                            leanh::lean_dec(v_unused_2377_);
                                            v___x_2365_ = v_l_1759_;
                                            v_isShared_2366_ = v_isSharedCheck_2374_;
                                            state = 89;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2363_);
                                            leanh::lean_inc(v_k_2362_);
                                            leanh::lean_dec(v_l_1759_);
                                            v___x_2365_ = leanh::lean_box(0);
                                            v_isShared_2366_ = v_isSharedCheck_2374_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2378_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                    leanh::lean_inc(v_r_2378_);
                                    if leanh::lean_obj_tag(v_r_2378_) == 0 {
                                        leanh::lean_inc(v_l_2342_);
                                        v_k_2379_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                        v_v_2380_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                        v_isSharedCheck_2403_ =
                                            (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                                        if v_isSharedCheck_2403_ == 0 {
                                            v_unused_2404_ =
                                                leanh::lean_ctor_get(v_l_1759_, 4);
                                            leanh::lean_dec(v_unused_2404_);
                                            v_unused_2405_ =
                                                leanh::lean_ctor_get(v_l_1759_, 3);
                                            leanh::lean_dec(v_unused_2405_);
                                            v_unused_2406_ =
                                                leanh::lean_ctor_get(v_l_1759_, 0);
                                            leanh::lean_dec(v_unused_2406_);
                                            v___x_2382_ = v_l_1759_;
                                            v_isShared_2383_ = v_isSharedCheck_2403_;
                                            state = 92;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2380_);
                                            leanh::lean_inc(v_k_2379_);
                                            leanh::lean_dec(v_l_1759_);
                                            v___x_2382_ = leanh::lean_box(0);
                                            v_isShared_2383_ = v_isSharedCheck_2403_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_2407_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1763_ == 0 {
                                            leanh::lean_ctor_set(v___x_1762_, 4, v_r_2378_);
                                            leanh::lean_ctor_set(
                                                v___x_1762_,
                                                0,
                                                v___x_2407_,
                                            );
                                            v___x_2409_ = v___x_1762_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2410_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2410_,
                                                0,
                                                v___x_2407_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2410_,
                                                1,
                                                v_k_1757_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2410_,
                                                2,
                                                v_v_1758_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2410_,
                                                3,
                                                v_l_1759_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2410_,
                                                4,
                                                v_r_2378_,
                                            );
                                            v___x_2409_ = v_reuseFailAlloc_2410_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_1763_ == 0 {
                                    leanh::lean_ctor_set(v___x_1762_, 4, v_l_1759_);
                                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_2251_);
                                    v___x_2412_ = v___x_1762_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2413_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2413_,
                                        0,
                                        v___x_2251_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2413_,
                                        1,
                                        v_k_1757_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2413_,
                                        2,
                                        v_v_1758_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2413_,
                                        3,
                                        v_l_1759_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2413_,
                                        4,
                                        v_l_1759_,
                                    );
                                    v___x_2412_ = v_reuseFailAlloc_2413_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1779_;
            }
            3 => {
                v_size_1784_ = leanh::lean_ctor_get(v_l_1771_, 0);
                v_k_1785_ = leanh::lean_ctor_get(v_l_1771_, 1);
                v_v_1786_ = leanh::lean_ctor_get(v_l_1771_, 2);
                v_l_1787_ = leanh::lean_ctor_get(v_l_1771_, 3);
                v_r_1788_ = leanh::lean_ctor_get(v_l_1771_, 4);
                v_size_1789_ = leanh::lean_ctor_get(v_r_1772_, 0);
                v___x_1790_ = leanh::lean_unsigned_to_nat(2);
                v___x_1791_ = lean_nat_mul(v___x_1790_, v_size_1789_);
                v___x_1792_ = lean_nat_dec_lt(v_size_1784_, v___x_1791_);
                leanh::lean_dec(v___x_1791_);
                if v___x_1792_ == 0 {
                    leanh::lean_inc(v_r_1788_);
                    leanh::lean_inc(v_l_1787_);
                    leanh::lean_inc(v_v_1786_);
                    leanh::lean_inc(v_k_1785_);
                    v_isSharedCheck_1820_ = (!leanh::lean_is_exclusive(v_l_1771_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v_unused_1821_ = leanh::lean_ctor_get(v_l_1771_, 4);
                        leanh::lean_dec(v_unused_1821_);
                        v_unused_1822_ = leanh::lean_ctor_get(v_l_1771_, 3);
                        leanh::lean_dec(v_unused_1822_);
                        v_unused_1823_ = leanh::lean_ctor_get(v_l_1771_, 2);
                        leanh::lean_dec(v_unused_1823_);
                        v_unused_1824_ = leanh::lean_ctor_get(v_l_1771_, 1);
                        leanh::lean_dec(v_unused_1824_);
                        v_unused_1825_ = leanh::lean_ctor_get(v_l_1771_, 0);
                        leanh::lean_dec(v_unused_1825_);
                        v___x_1794_ = v_l_1771_;
                        v_isShared_1795_ = v_isSharedCheck_1820_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1771_);
                        v___x_1794_ = leanh::lean_box(0);
                        v_isShared_1795_ = v_isSharedCheck_1820_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1762_);
                    v___x_1826_ = lean_nat_add(v___x_1766_, v_size_1767_);
                    leanh::lean_dec(v_size_1767_);
                    v___x_1827_ = lean_nat_add(v___x_1826_, v_size_1768_);
                    leanh::lean_dec(v_size_1768_);
                    v___x_1828_ = lean_nat_add(v___x_1826_, v_size_1784_);
                    leanh::lean_dec(v___x_1826_);
                    leanh::lean_inc_ref(v_impl_1765_);
                    if v_isShared_1783_ == 0 {
                        leanh::lean_ctor_set(v___x_1782_, 4, v_l_1771_);
                        leanh::lean_ctor_set(v___x_1782_, 3, v_impl_1765_);
                        leanh::lean_ctor_set(v___x_1782_, 2, v_v_1758_);
                        leanh::lean_ctor_set(v___x_1782_, 1, v_k_1757_);
                        leanh::lean_ctor_set(v___x_1782_, 0, v___x_1828_);
                        v___x_1830_ = v___x_1782_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1843_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1828_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_k_1757_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_v_1758_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_impl_1765_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_l_1771_);
                        v___x_1830_ = v_reuseFailAlloc_1843_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1796_ = lean_nat_add(v___x_1766_, v_size_1767_);
                leanh::lean_dec(v_size_1767_);
                v___x_1797_ = lean_nat_add(v___x_1796_, v_size_1768_);
                leanh::lean_dec(v_size_1768_);
                if leanh::lean_obj_tag(v_l_1787_) == 0 {
                    v_size_1818_ = leanh::lean_ctor_get(v_l_1787_, 0);
                    leanh::lean_inc(v_size_1818_);
                    v___y_1810_ = v_size_1818_;
                    state = 8;
                    continue;
                } else {
                    v___x_1819_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1810_ = v___x_1819_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1802_ = lean_nat_add(v___y_1800_, v___y_1801_);
                leanh::lean_dec(v___y_1801_);
                leanh::lean_dec(v___y_1800_);
                if v_isShared_1795_ == 0 {
                    leanh::lean_ctor_set(v___x_1794_, 4, v_r_1772_);
                    leanh::lean_ctor_set(v___x_1794_, 3, v_r_1788_);
                    leanh::lean_ctor_set(v___x_1794_, 2, v_v_1770_);
                    leanh::lean_ctor_set(v___x_1794_, 1, v_k_1769_);
                    leanh::lean_ctor_set(v___x_1794_, 0, v___x_1802_);
                    v___x_1804_ = v___x_1794_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_k_1769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_v_1770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_r_1788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_r_1772_);
                    v___x_1804_ = v_reuseFailAlloc_1808_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1783_ == 0 {
                    leanh::lean_ctor_set(v___x_1782_, 4, v___x_1804_);
                    leanh::lean_ctor_set(v___x_1782_, 3, v___y_1799_);
                    leanh::lean_ctor_set(v___x_1782_, 2, v_v_1786_);
                    leanh::lean_ctor_set(v___x_1782_, 1, v_k_1785_);
                    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1797_);
                    v___x_1806_ = v___x_1782_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_k_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_v_1786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 3, v___y_1799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 4, v___x_1804_);
                    v___x_1806_ = v_reuseFailAlloc_1807_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1806_;
            }
            8 => {
                v___x_1811_ = lean_nat_add(v___x_1796_, v___y_1810_);
                leanh::lean_dec(v___y_1810_);
                leanh::lean_dec(v___x_1796_);
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v_l_1787_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v_impl_1765_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1811_);
                    v___x_1813_ = v___x_1762_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1817_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_impl_1765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_l_1787_);
                    v___x_1813_ = v_reuseFailAlloc_1817_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1814_ = lean_nat_add(v___x_1766_, v_size_1789_);
                if leanh::lean_obj_tag(v_r_1788_) == 0 {
                    v_size_1815_ = leanh::lean_ctor_get(v_r_1788_, 0);
                    leanh::lean_inc(v_size_1815_);
                    v___y_1799_ = v___x_1813_;
                    v___y_1800_ = v___x_1814_;
                    v___y_1801_ = v_size_1815_;
                    state = 5;
                    continue;
                } else {
                    v___x_1816_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1799_ = v___x_1813_;
                    v___y_1800_ = v___x_1814_;
                    v___y_1801_ = v___x_1816_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1837_ = (!leanh::lean_is_exclusive(v_impl_1765_)) as u8;
                if v_isSharedCheck_1837_ == 0 {
                    v_unused_1838_ = leanh::lean_ctor_get(v_impl_1765_, 4);
                    leanh::lean_dec(v_unused_1838_);
                    v_unused_1839_ = leanh::lean_ctor_get(v_impl_1765_, 3);
                    leanh::lean_dec(v_unused_1839_);
                    v_unused_1840_ = leanh::lean_ctor_get(v_impl_1765_, 2);
                    leanh::lean_dec(v_unused_1840_);
                    v_unused_1841_ = leanh::lean_ctor_get(v_impl_1765_, 1);
                    leanh::lean_dec(v_unused_1841_);
                    v_unused_1842_ = leanh::lean_ctor_get(v_impl_1765_, 0);
                    leanh::lean_dec(v_unused_1842_);
                    v___x_1832_ = v_impl_1765_;
                    v_isShared_1833_ = v_isSharedCheck_1837_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_1765_);
                    v___x_1832_ = leanh::lean_box(0);
                    v_isShared_1833_ = v_isSharedCheck_1837_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1833_ == 0 {
                    leanh::lean_ctor_set(v___x_1832_, 4, v_r_1772_);
                    leanh::lean_ctor_set(v___x_1832_, 3, v___x_1830_);
                    leanh::lean_ctor_set(v___x_1832_, 2, v_v_1770_);
                    leanh::lean_ctor_set(v___x_1832_, 1, v_k_1769_);
                    leanh::lean_ctor_set(v___x_1832_, 0, v___x_1827_);
                    v___x_1835_ = v___x_1832_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_k_1769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_v_1770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 3, v___x_1830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 4, v_r_1772_);
                    v___x_1835_ = v_reuseFailAlloc_1836_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1835_;
            }
            13 => {
                return v___x_1853_;
            }
            14 => {
                v_size_1863_ = leanh::lean_ctor_get(v_l_1855_, 0);
                v___x_1864_ = lean_nat_add(v___x_1766_, v_size_1857_);
                leanh::lean_dec(v_size_1857_);
                v___x_1865_ = lean_nat_add(v___x_1766_, v_size_1863_);
                if v_isShared_1862_ == 0 {
                    leanh::lean_ctor_set(v___x_1861_, 4, v_l_1855_);
                    leanh::lean_ctor_set(v___x_1861_, 3, v_impl_1765_);
                    leanh::lean_ctor_set(v___x_1861_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_1861_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_1861_, 0, v___x_1865_);
                    v___x_1867_ = v___x_1861_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_impl_1765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_l_1855_);
                    v___x_1867_ = v_reuseFailAlloc_1871_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v_r_1856_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v___x_1867_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_1859_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_1858_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1864_);
                    v___x_1869_ = v___x_1762_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_k_1858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_v_1859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 3, v___x_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 4, v_r_1856_);
                    v___x_1869_ = v_reuseFailAlloc_1870_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1869_;
            }
            17 => {
                v_k_1880_ = leanh::lean_ctor_get(v_l_1855_, 1);
                v_v_1881_ = leanh::lean_ctor_get(v_l_1855_, 2);
                v_isSharedCheck_1895_ = (!leanh::lean_is_exclusive(v_l_1855_)) as u8;
                if v_isSharedCheck_1895_ == 0 {
                    v_unused_1896_ = leanh::lean_ctor_get(v_l_1855_, 4);
                    leanh::lean_dec(v_unused_1896_);
                    v_unused_1897_ = leanh::lean_ctor_get(v_l_1855_, 3);
                    leanh::lean_dec(v_unused_1897_);
                    v_unused_1898_ = leanh::lean_ctor_get(v_l_1855_, 0);
                    leanh::lean_dec(v_unused_1898_);
                    v___x_1883_ = v_l_1855_;
                    v_isShared_1884_ = v_isSharedCheck_1895_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1881_);
                    leanh::lean_inc(v_k_1880_);
                    leanh::lean_dec(v_l_1855_);
                    v___x_1883_ = leanh::lean_box(0);
                    v_isShared_1884_ = v_isSharedCheck_1895_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1885_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1884_ == 0 {
                    leanh::lean_ctor_set(v___x_1883_, 4, v_r_1856_);
                    leanh::lean_ctor_set(v___x_1883_, 3, v_r_1856_);
                    leanh::lean_ctor_set(v___x_1883_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_1883_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_1883_, 0, v___x_1766_);
                    v___x_1887_ = v___x_1883_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_r_1856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_r_1856_);
                    v___x_1887_ = v_reuseFailAlloc_1894_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1879_ == 0 {
                    leanh::lean_ctor_set(v___x_1878_, 3, v_r_1856_);
                    leanh::lean_ctor_set(v___x_1878_, 0, v___x_1766_);
                    v___x_1889_ = v___x_1878_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_k_1875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_v_1876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_r_1856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 4, v_r_1856_);
                    v___x_1889_ = v_reuseFailAlloc_1893_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v___x_1889_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v___x_1887_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_1881_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_1880_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1885_);
                    v___x_1891_ = v___x_1762_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 3, v___x_1887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 4, v___x_1889_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1891_;
            }
            22 => {
                v___x_1909_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1908_ == 0 {
                    leanh::lean_ctor_set(v___x_1907_, 4, v_l_1855_);
                    leanh::lean_ctor_set(v___x_1907_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_1907_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_1907_, 0, v___x_1766_);
                    v___x_1911_ = v___x_1907_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_l_1855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_l_1855_);
                    v___x_1911_ = v_reuseFailAlloc_1915_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v_r_1903_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v___x_1911_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_1905_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_1904_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1909_);
                    v___x_1913_ = v___x_1762_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_k_1904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_v_1905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 3, v___x_1911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_r_1903_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1913_;
            }
            25 => {
                if v_isShared_1925_ == 0 {
                    leanh::lean_ctor_set(v___x_1924_, 3, v_r_1903_);
                    v___x_1927_ = v___x_1924_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_size_1920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_r_1903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_r_1903_);
                    v___x_1927_ = v_reuseFailAlloc_1932_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_1928_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v___x_1927_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v_r_1903_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1762_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_r_1903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 4, v___x_1927_);
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1930_;
            }
            28 => {
                return v___x_1937_;
            }
            29 => {
                v___x_1954_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_1940_, v_v_1941_, v_l_1942_, v_r_1943_,
                );
                v_tree_1955_ = leanh::lean_ctor_get(v___x_1954_, 2);
                leanh::lean_inc(v_tree_1955_);
                if leanh::lean_obj_tag(v_tree_1955_) == 0 {
                    v_k_1956_ = leanh::lean_ctor_get(v___x_1954_, 0);
                    leanh::lean_inc(v_k_1956_);
                    v_v_1957_ = leanh::lean_ctor_get(v___x_1954_, 1);
                    leanh::lean_inc(v_v_1957_);
                    leanh::lean_dec_ref(v___x_1954_);
                    v_size_1958_ = leanh::lean_ctor_get(v_tree_1955_, 0);
                    v___x_1959_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1960_ = lean_nat_mul(v___x_1959_, v_size_1958_);
                    v___x_1961_ = lean_nat_dec_lt(v___x_1960_, v_size_1944_);
                    leanh::lean_dec(v___x_1960_);
                    if v___x_1961_ == 0 {
                        leanh::lean_dec(v_l_1947_);
                        v___x_1962_ = lean_nat_add(v___x_1949_, v_size_1958_);
                        v___x_1963_ = lean_nat_add(v___x_1962_, v_size_1944_);
                        leanh::lean_dec(v___x_1962_);
                        if v_isShared_1953_ == 0 {
                            leanh::lean_ctor_set(v___x_1952_, 4, v_r_1760_);
                            leanh::lean_ctor_set(v___x_1952_, 3, v_tree_1955_);
                            leanh::lean_ctor_set(v___x_1952_, 2, v_v_1957_);
                            leanh::lean_ctor_set(v___x_1952_, 1, v_k_1956_);
                            leanh::lean_ctor_set(v___x_1952_, 0, v___x_1963_);
                            v___x_1965_ = v___x_1952_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_1966_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_k_1956_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_v_1957_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_tree_1955_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_r_1760_);
                            v___x_1965_ = v_reuseFailAlloc_1966_;
                            state = 30;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_r_1948_);
                        leanh::lean_inc(v_v_1946_);
                        leanh::lean_inc(v_k_1945_);
                        leanh::lean_inc(v_size_1944_);
                        v_isSharedCheck_2021_ = (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                        if v_isSharedCheck_2021_ == 0 {
                            v_unused_2022_ = leanh::lean_ctor_get(v_r_1760_, 4);
                            leanh::lean_dec(v_unused_2022_);
                            v_unused_2023_ = leanh::lean_ctor_get(v_r_1760_, 3);
                            leanh::lean_dec(v_unused_2023_);
                            v_unused_2024_ = leanh::lean_ctor_get(v_r_1760_, 2);
                            leanh::lean_dec(v_unused_2024_);
                            v_unused_2025_ = leanh::lean_ctor_get(v_r_1760_, 1);
                            leanh::lean_dec(v_unused_2025_);
                            v_unused_2026_ = leanh::lean_ctor_get(v_r_1760_, 0);
                            leanh::lean_dec(v_unused_2026_);
                            v___x_1968_ = v_r_1760_;
                            v_isShared_1969_ = v_isSharedCheck_2021_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_1760_);
                            v___x_1968_ = leanh::lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_2021_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_r_1948_);
                    leanh::lean_inc(v_v_1946_);
                    leanh::lean_inc(v_k_1945_);
                    leanh::lean_inc(v_size_1944_);
                    v_isSharedCheck_2080_ = (!leanh::lean_is_exclusive(v_r_1760_)) as u8;
                    if v_isSharedCheck_2080_ == 0 {
                        v_unused_2081_ = leanh::lean_ctor_get(v_r_1760_, 4);
                        leanh::lean_dec(v_unused_2081_);
                        v_unused_2082_ = leanh::lean_ctor_get(v_r_1760_, 3);
                        leanh::lean_dec(v_unused_2082_);
                        v_unused_2083_ = leanh::lean_ctor_get(v_r_1760_, 2);
                        leanh::lean_dec(v_unused_2083_);
                        v_unused_2084_ = leanh::lean_ctor_get(v_r_1760_, 1);
                        leanh::lean_dec(v_unused_2084_);
                        v_unused_2085_ = leanh::lean_ctor_get(v_r_1760_, 0);
                        leanh::lean_dec(v_unused_2085_);
                        v___x_2028_ = v_r_1760_;
                        v_isShared_2029_ = v_isSharedCheck_2080_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1760_);
                        v___x_2028_ = leanh::lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2080_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_1965_;
            }
            31 => {
                v_size_1970_ = leanh::lean_ctor_get(v_l_1947_, 0);
                v_k_1971_ = leanh::lean_ctor_get(v_l_1947_, 1);
                v_v_1972_ = leanh::lean_ctor_get(v_l_1947_, 2);
                v_l_1973_ = leanh::lean_ctor_get(v_l_1947_, 3);
                v_r_1974_ = leanh::lean_ctor_get(v_l_1947_, 4);
                v_size_1975_ = leanh::lean_ctor_get(v_r_1948_, 0);
                v___x_1976_ = leanh::lean_unsigned_to_nat(2);
                v___x_1977_ = lean_nat_mul(v___x_1976_, v_size_1975_);
                v___x_1978_ = lean_nat_dec_lt(v_size_1970_, v___x_1977_);
                leanh::lean_dec(v___x_1977_);
                if v___x_1978_ == 0 {
                    leanh::lean_inc(v_r_1974_);
                    leanh::lean_inc(v_l_1973_);
                    leanh::lean_inc(v_v_1972_);
                    leanh::lean_inc(v_k_1971_);
                    v_isSharedCheck_2006_ = (!leanh::lean_is_exclusive(v_l_1947_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v_unused_2007_ = leanh::lean_ctor_get(v_l_1947_, 4);
                        leanh::lean_dec(v_unused_2007_);
                        v_unused_2008_ = leanh::lean_ctor_get(v_l_1947_, 3);
                        leanh::lean_dec(v_unused_2008_);
                        v_unused_2009_ = leanh::lean_ctor_get(v_l_1947_, 2);
                        leanh::lean_dec(v_unused_2009_);
                        v_unused_2010_ = leanh::lean_ctor_get(v_l_1947_, 1);
                        leanh::lean_dec(v_unused_2010_);
                        v_unused_2011_ = leanh::lean_ctor_get(v_l_1947_, 0);
                        leanh::lean_dec(v_unused_2011_);
                        v___x_1980_ = v_l_1947_;
                        v_isShared_1981_ = v_isSharedCheck_2006_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1947_);
                        v___x_1980_ = leanh::lean_box(0);
                        v_isShared_1981_ = v_isSharedCheck_2006_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_2012_ = lean_nat_add(v___x_1949_, v_size_1958_);
                    v___x_2013_ = lean_nat_add(v___x_2012_, v_size_1944_);
                    leanh::lean_dec(v_size_1944_);
                    v___x_2014_ = lean_nat_add(v___x_2012_, v_size_1970_);
                    leanh::lean_dec(v___x_2012_);
                    if v_isShared_1969_ == 0 {
                        leanh::lean_ctor_set(v___x_1968_, 4, v_l_1947_);
                        leanh::lean_ctor_set(v___x_1968_, 3, v_tree_1955_);
                        leanh::lean_ctor_set(v___x_1968_, 2, v_v_1957_);
                        leanh::lean_ctor_set(v___x_1968_, 1, v_k_1956_);
                        leanh::lean_ctor_set(v___x_1968_, 0, v___x_2014_);
                        v___x_2016_ = v___x_1968_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2020_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2014_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_1956_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_1957_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_tree_1955_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_l_1947_);
                        v___x_2016_ = v_reuseFailAlloc_2020_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_1982_ = lean_nat_add(v___x_1949_, v_size_1958_);
                v___x_1983_ = lean_nat_add(v___x_1982_, v_size_1944_);
                leanh::lean_dec(v_size_1944_);
                if leanh::lean_obj_tag(v_l_1973_) == 0 {
                    v_size_2004_ = leanh::lean_ctor_get(v_l_1973_, 0);
                    leanh::lean_inc(v_size_2004_);
                    v___y_1996_ = v_size_2004_;
                    state = 36;
                    continue;
                } else {
                    v___x_2005_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1996_ = v___x_2005_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_1988_ = lean_nat_add(v___y_1985_, v___y_1987_);
                leanh::lean_dec(v___y_1987_);
                leanh::lean_dec(v___y_1985_);
                if v_isShared_1981_ == 0 {
                    leanh::lean_ctor_set(v___x_1980_, 4, v_r_1948_);
                    leanh::lean_ctor_set(v___x_1980_, 3, v_r_1974_);
                    leanh::lean_ctor_set(v___x_1980_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v___x_1980_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v___x_1980_, 0, v___x_1988_);
                    v___x_1990_ = v___x_1980_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1994_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_r_1974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_r_1948_);
                    v___x_1990_ = v_reuseFailAlloc_1994_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_1969_ == 0 {
                    leanh::lean_ctor_set(v___x_1968_, 4, v___x_1990_);
                    leanh::lean_ctor_set(v___x_1968_, 3, v___y_1986_);
                    leanh::lean_ctor_set(v___x_1968_, 2, v_v_1972_);
                    leanh::lean_ctor_set(v___x_1968_, 1, v_k_1971_);
                    leanh::lean_ctor_set(v___x_1968_, 0, v___x_1983_);
                    v___x_1992_ = v___x_1968_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 3, v___y_1986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 4, v___x_1990_);
                    v___x_1992_ = v_reuseFailAlloc_1993_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1992_;
            }
            36 => {
                v___x_1997_ = lean_nat_add(v___x_1982_, v___y_1996_);
                leanh::lean_dec(v___y_1996_);
                leanh::lean_dec(v___x_1982_);
                if v_isShared_1953_ == 0 {
                    leanh::lean_ctor_set(v___x_1952_, 4, v_l_1973_);
                    leanh::lean_ctor_set(v___x_1952_, 3, v_tree_1955_);
                    leanh::lean_ctor_set(v___x_1952_, 2, v_v_1957_);
                    leanh::lean_ctor_set(v___x_1952_, 1, v_k_1956_);
                    leanh::lean_ctor_set(v___x_1952_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1952_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_tree_1955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_l_1973_);
                    v___x_1999_ = v_reuseFailAlloc_2003_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_2000_ = lean_nat_add(v___x_1949_, v_size_1975_);
                if leanh::lean_obj_tag(v_r_1974_) == 0 {
                    v_size_2001_ = leanh::lean_ctor_get(v_r_1974_, 0);
                    leanh::lean_inc(v_size_2001_);
                    v___y_1985_ = v___x_2000_;
                    v___y_1986_ = v___x_1999_;
                    v___y_1987_ = v_size_2001_;
                    state = 33;
                    continue;
                } else {
                    v___x_2002_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1985_ = v___x_2000_;
                    v___y_1986_ = v___x_1999_;
                    v___y_1987_ = v___x_2002_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_1953_ == 0 {
                    leanh::lean_ctor_set(v___x_1952_, 4, v_r_1948_);
                    leanh::lean_ctor_set(v___x_1952_, 3, v___x_2016_);
                    leanh::lean_ctor_set(v___x_1952_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v___x_1952_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v___x_1952_, 0, v___x_2013_);
                    v___x_2018_ = v___x_1952_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 3, v___x_2016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_r_1948_);
                    v___x_2018_ = v_reuseFailAlloc_2019_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2018_;
            }
            40 => {
                if leanh::lean_obj_tag(v_l_1947_) == 0 {
                    if leanh::lean_obj_tag(v_r_1948_) == 0 {
                        v_k_2030_ = leanh::lean_ctor_get(v___x_1954_, 0);
                        leanh::lean_inc(v_k_2030_);
                        v_v_2031_ = leanh::lean_ctor_get(v___x_1954_, 1);
                        leanh::lean_inc(v_v_2031_);
                        leanh::lean_dec_ref(v___x_1954_);
                        v_size_2032_ = leanh::lean_ctor_get(v_l_1947_, 0);
                        v___x_2033_ = lean_nat_add(v___x_1949_, v_size_1944_);
                        leanh::lean_dec(v_size_1944_);
                        v___x_2034_ = lean_nat_add(v___x_1949_, v_size_2032_);
                        if v_isShared_2029_ == 0 {
                            leanh::lean_ctor_set(v___x_2028_, 4, v_l_1947_);
                            leanh::lean_ctor_set(v___x_2028_, 3, v_tree_1955_);
                            leanh::lean_ctor_set(v___x_2028_, 2, v_v_2031_);
                            leanh::lean_ctor_set(v___x_2028_, 1, v_k_2030_);
                            leanh::lean_ctor_set(v___x_2028_, 0, v___x_2034_);
                            v___x_2036_ = v___x_2028_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_2040_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2034_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_2030_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_2031_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_tree_1955_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_l_1947_);
                            v___x_2036_ = v_reuseFailAlloc_2040_;
                            state = 41;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_size_1944_);
                        v_k_2041_ = leanh::lean_ctor_get(v___x_1954_, 0);
                        leanh::lean_inc(v_k_2041_);
                        v_v_2042_ = leanh::lean_ctor_get(v___x_1954_, 1);
                        leanh::lean_inc(v_v_2042_);
                        leanh::lean_dec_ref(v___x_1954_);
                        v_k_2043_ = leanh::lean_ctor_get(v_l_1947_, 1);
                        v_v_2044_ = leanh::lean_ctor_get(v_l_1947_, 2);
                        v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v_l_1947_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v_unused_2059_ = leanh::lean_ctor_get(v_l_1947_, 4);
                            leanh::lean_dec(v_unused_2059_);
                            v_unused_2060_ = leanh::lean_ctor_get(v_l_1947_, 3);
                            leanh::lean_dec(v_unused_2060_);
                            v_unused_2061_ = leanh::lean_ctor_get(v_l_1947_, 0);
                            leanh::lean_dec(v_unused_2061_);
                            v___x_2046_ = v_l_1947_;
                            v_isShared_2047_ = v_isSharedCheck_2058_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_2044_);
                            leanh::lean_inc(v_k_2043_);
                            leanh::lean_dec(v_l_1947_);
                            v___x_2046_ = leanh::lean_box(0);
                            v_isShared_2047_ = v_isSharedCheck_2058_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_r_1948_) == 0 {
                        leanh::lean_dec(v_size_1944_);
                        v_k_2062_ = leanh::lean_ctor_get(v___x_1954_, 0);
                        leanh::lean_inc(v_k_2062_);
                        v_v_2063_ = leanh::lean_ctor_get(v___x_1954_, 1);
                        leanh::lean_inc(v_v_2063_);
                        leanh::lean_dec_ref(v___x_1954_);
                        v___x_2064_ = leanh::lean_unsigned_to_nat(3);
                        if v_isShared_2029_ == 0 {
                            leanh::lean_ctor_set(v___x_2028_, 4, v_l_1947_);
                            leanh::lean_ctor_set(v___x_2028_, 2, v_v_2063_);
                            leanh::lean_ctor_set(v___x_2028_, 1, v_k_2062_);
                            leanh::lean_ctor_set(v___x_2028_, 0, v___x_1949_);
                            v___x_2066_ = v___x_2028_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2070_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_1949_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_k_2062_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_v_2063_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_l_1947_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 4, v_l_1947_);
                            v___x_2066_ = v_reuseFailAlloc_2070_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_2071_ = leanh::lean_ctor_get(v___x_1954_, 0);
                        leanh::lean_inc(v_k_2071_);
                        v_v_2072_ = leanh::lean_ctor_get(v___x_1954_, 1);
                        leanh::lean_inc(v_v_2072_);
                        leanh::lean_dec_ref(v___x_1954_);
                        if v_isShared_2029_ == 0 {
                            leanh::lean_ctor_set(v___x_2028_, 3, v_r_1948_);
                            v___x_2074_ = v___x_2028_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2079_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_size_1944_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_1945_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_1946_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_r_1948_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_r_1948_);
                            v___x_2074_ = v_reuseFailAlloc_2079_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_1953_ == 0 {
                    leanh::lean_ctor_set(v___x_1952_, 4, v_r_1948_);
                    leanh::lean_ctor_set(v___x_1952_, 3, v___x_2036_);
                    leanh::lean_ctor_set(v___x_1952_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v___x_1952_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v___x_1952_, 0, v___x_2033_);
                    v___x_2038_ = v___x_1952_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2039_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 3, v___x_2036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_r_1948_);
                    v___x_2038_ = v_reuseFailAlloc_2039_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2038_;
            }
            43 => {
                v___x_2048_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2047_ == 0 {
                    leanh::lean_ctor_set(v___x_2046_, 4, v_r_1948_);
                    leanh::lean_ctor_set(v___x_2046_, 3, v_r_1948_);
                    leanh::lean_ctor_set(v___x_2046_, 2, v_v_2042_);
                    leanh::lean_ctor_set(v___x_2046_, 1, v_k_2041_);
                    leanh::lean_ctor_set(v___x_2046_, 0, v___x_1949_);
                    v___x_2050_ = v___x_2046_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_2041_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_2042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_r_1948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_r_1948_);
                    v___x_2050_ = v_reuseFailAlloc_2057_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2029_ == 0 {
                    leanh::lean_ctor_set(v___x_2028_, 3, v_r_1948_);
                    leanh::lean_ctor_set(v___x_2028_, 0, v___x_1949_);
                    v___x_2052_ = v___x_2028_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_r_1948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_r_1948_);
                    v___x_2052_ = v_reuseFailAlloc_2056_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1953_ == 0 {
                    leanh::lean_ctor_set(v___x_1952_, 4, v___x_2052_);
                    leanh::lean_ctor_set(v___x_1952_, 3, v___x_2050_);
                    leanh::lean_ctor_set(v___x_1952_, 2, v_v_2044_);
                    leanh::lean_ctor_set(v___x_1952_, 1, v_k_2043_);
                    leanh::lean_ctor_set(v___x_1952_, 0, v___x_2048_);
                    v___x_2054_ = v___x_1952_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_k_2043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_v_2044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 3, v___x_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 4, v___x_2052_);
                    v___x_2054_ = v_reuseFailAlloc_2055_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2054_;
            }
            47 => {
                if v_isShared_1953_ == 0 {
                    leanh::lean_ctor_set(v___x_1952_, 4, v_r_1948_);
                    leanh::lean_ctor_set(v___x_1952_, 3, v___x_2066_);
                    leanh::lean_ctor_set(v___x_1952_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v___x_1952_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v___x_1952_, 0, v___x_2064_);
                    v___x_2068_ = v___x_1952_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 3, v___x_2066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_r_1948_);
                    v___x_2068_ = v_reuseFailAlloc_2069_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2068_;
            }
            49 => {
                v___x_2075_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_1953_ == 0 {
                    leanh::lean_ctor_set(v___x_1952_, 4, v___x_2074_);
                    leanh::lean_ctor_set(v___x_1952_, 3, v_r_1948_);
                    leanh::lean_ctor_set(v___x_1952_, 2, v_v_2072_);
                    leanh::lean_ctor_set(v___x_1952_, 1, v_k_2071_);
                    leanh::lean_ctor_set(v___x_1952_, 0, v___x_2075_);
                    v___x_2077_ = v___x_1952_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_2071_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_2072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_r_1948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___x_2074_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2077_;
            }
            51 => {
                v___x_2095_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_1945_, v_v_1946_, v_l_1947_, v_r_1948_,
                );
                v_tree_2096_ = leanh::lean_ctor_get(v___x_2095_, 2);
                leanh::lean_inc(v_tree_2096_);
                if leanh::lean_obj_tag(v_tree_2096_) == 0 {
                    v_k_2097_ = leanh::lean_ctor_get(v___x_2095_, 0);
                    leanh::lean_inc(v_k_2097_);
                    v_v_2098_ = leanh::lean_ctor_get(v___x_2095_, 1);
                    leanh::lean_inc(v_v_2098_);
                    leanh::lean_dec_ref(v___x_2095_);
                    v_size_2099_ = leanh::lean_ctor_get(v_tree_2096_, 0);
                    v___x_2100_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2101_ = lean_nat_mul(v___x_2100_, v_size_2099_);
                    v___x_2102_ = lean_nat_dec_lt(v___x_2101_, v_size_1939_);
                    leanh::lean_dec(v___x_2101_);
                    if v___x_2102_ == 0 {
                        leanh::lean_dec(v_r_1943_);
                        v___x_2103_ = lean_nat_add(v___x_1949_, v_size_1939_);
                        v___x_2104_ = lean_nat_add(v___x_2103_, v_size_2099_);
                        leanh::lean_dec(v___x_2103_);
                        if v_isShared_2094_ == 0 {
                            leanh::lean_ctor_set(v___x_2093_, 4, v_tree_2096_);
                            leanh::lean_ctor_set(v___x_2093_, 3, v_l_1759_);
                            leanh::lean_ctor_set(v___x_2093_, 2, v_v_2098_);
                            leanh::lean_ctor_set(v___x_2093_, 1, v_k_2097_);
                            leanh::lean_ctor_set(v___x_2093_, 0, v___x_2104_);
                            v___x_2106_ = v___x_2093_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_2107_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_k_2097_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_v_2098_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_l_1759_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 4, v_tree_2096_);
                            v___x_2106_ = v_reuseFailAlloc_2107_;
                            state = 52;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_l_1942_);
                        leanh::lean_inc(v_v_1941_);
                        leanh::lean_inc(v_k_1940_);
                        leanh::lean_inc(v_size_1939_);
                        v_isSharedCheck_2173_ = (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                        if v_isSharedCheck_2173_ == 0 {
                            v_unused_2174_ = leanh::lean_ctor_get(v_l_1759_, 4);
                            leanh::lean_dec(v_unused_2174_);
                            v_unused_2175_ = leanh::lean_ctor_get(v_l_1759_, 3);
                            leanh::lean_dec(v_unused_2175_);
                            v_unused_2176_ = leanh::lean_ctor_get(v_l_1759_, 2);
                            leanh::lean_dec(v_unused_2176_);
                            v_unused_2177_ = leanh::lean_ctor_get(v_l_1759_, 1);
                            leanh::lean_dec(v_unused_2177_);
                            v_unused_2178_ = leanh::lean_ctor_get(v_l_1759_, 0);
                            leanh::lean_dec(v_unused_2178_);
                            v___x_2109_ = v_l_1759_;
                            v_isShared_2110_ = v_isSharedCheck_2173_;
                            state = 53;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_1759_);
                            v___x_2109_ = leanh::lean_box(0);
                            v_isShared_2110_ = v_isSharedCheck_2173_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_1942_) == 0 {
                        leanh::lean_inc_ref(v_l_1942_);
                        leanh::lean_inc(v_v_1941_);
                        leanh::lean_inc(v_k_1940_);
                        leanh::lean_inc(v_size_1939_);
                        v_isSharedCheck_2202_ = (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                        if v_isSharedCheck_2202_ == 0 {
                            v_unused_2203_ = leanh::lean_ctor_get(v_l_1759_, 4);
                            leanh::lean_dec(v_unused_2203_);
                            v_unused_2204_ = leanh::lean_ctor_get(v_l_1759_, 3);
                            leanh::lean_dec(v_unused_2204_);
                            v_unused_2205_ = leanh::lean_ctor_get(v_l_1759_, 2);
                            leanh::lean_dec(v_unused_2205_);
                            v_unused_2206_ = leanh::lean_ctor_get(v_l_1759_, 1);
                            leanh::lean_dec(v_unused_2206_);
                            v_unused_2207_ = leanh::lean_ctor_get(v_l_1759_, 0);
                            leanh::lean_dec(v_unused_2207_);
                            v___x_2180_ = v_l_1759_;
                            v_isShared_2181_ = v_isSharedCheck_2202_;
                            state = 63;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_1759_);
                            v___x_2180_ = leanh::lean_box(0);
                            v_isShared_2181_ = v_isSharedCheck_2202_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_1943_) == 0 {
                            leanh::lean_inc(v_l_1942_);
                            leanh::lean_inc(v_v_1941_);
                            leanh::lean_inc(v_k_1940_);
                            v_isSharedCheck_2232_ =
                                (!leanh::lean_is_exclusive(v_l_1759_)) as u8;
                            if v_isSharedCheck_2232_ == 0 {
                                v_unused_2233_ = leanh::lean_ctor_get(v_l_1759_, 4);
                                leanh::lean_dec(v_unused_2233_);
                                v_unused_2234_ = leanh::lean_ctor_get(v_l_1759_, 3);
                                leanh::lean_dec(v_unused_2234_);
                                v_unused_2235_ = leanh::lean_ctor_get(v_l_1759_, 2);
                                leanh::lean_dec(v_unused_2235_);
                                v_unused_2236_ = leanh::lean_ctor_get(v_l_1759_, 1);
                                leanh::lean_dec(v_unused_2236_);
                                v_unused_2237_ = leanh::lean_ctor_get(v_l_1759_, 0);
                                leanh::lean_dec(v_unused_2237_);
                                v___x_2209_ = v_l_1759_;
                                v_isShared_2210_ = v_isSharedCheck_2232_;
                                state = 68;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_1759_);
                                v___x_2209_ = leanh::lean_box(0);
                                v_isShared_2210_ = v_isSharedCheck_2232_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_2238_ = leanh::lean_ctor_get(v___x_2095_, 0);
                            leanh::lean_inc(v_k_2238_);
                            v_v_2239_ = leanh::lean_ctor_get(v___x_2095_, 1);
                            leanh::lean_inc(v_v_2239_);
                            leanh::lean_dec_ref(v___x_2095_);
                            v___x_2240_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2094_ == 0 {
                                leanh::lean_ctor_set(v___x_2093_, 4, v_r_1943_);
                                leanh::lean_ctor_set(v___x_2093_, 3, v_l_1759_);
                                leanh::lean_ctor_set(v___x_2093_, 2, v_v_2239_);
                                leanh::lean_ctor_set(v___x_2093_, 1, v_k_2238_);
                                leanh::lean_ctor_set(v___x_2093_, 0, v___x_2240_);
                                v___x_2242_ = v___x_2093_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_2243_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_k_2238_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_v_2239_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_l_1759_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_r_1943_);
                                v___x_2242_ = v_reuseFailAlloc_2243_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_2106_;
            }
            53 => {
                v_size_2111_ = leanh::lean_ctor_get(v_l_1942_, 0);
                v_size_2112_ = leanh::lean_ctor_get(v_r_1943_, 0);
                v_k_2113_ = leanh::lean_ctor_get(v_r_1943_, 1);
                v_v_2114_ = leanh::lean_ctor_get(v_r_1943_, 2);
                v_l_2115_ = leanh::lean_ctor_get(v_r_1943_, 3);
                v_r_2116_ = leanh::lean_ctor_get(v_r_1943_, 4);
                v___x_2117_ = leanh::lean_unsigned_to_nat(2);
                v___x_2118_ = lean_nat_mul(v___x_2117_, v_size_2111_);
                v___x_2119_ = lean_nat_dec_lt(v_size_2112_, v___x_2118_);
                leanh::lean_dec(v___x_2118_);
                if v___x_2119_ == 0 {
                    leanh::lean_inc(v_r_2116_);
                    leanh::lean_inc(v_l_2115_);
                    leanh::lean_inc(v_v_2114_);
                    leanh::lean_inc(v_k_2113_);
                    leanh::lean_del_object(v___x_2109_);
                    v_isSharedCheck_2157_ = (!leanh::lean_is_exclusive(v_r_1943_)) as u8;
                    if v_isSharedCheck_2157_ == 0 {
                        v_unused_2158_ = leanh::lean_ctor_get(v_r_1943_, 4);
                        leanh::lean_dec(v_unused_2158_);
                        v_unused_2159_ = leanh::lean_ctor_get(v_r_1943_, 3);
                        leanh::lean_dec(v_unused_2159_);
                        v_unused_2160_ = leanh::lean_ctor_get(v_r_1943_, 2);
                        leanh::lean_dec(v_unused_2160_);
                        v_unused_2161_ = leanh::lean_ctor_get(v_r_1943_, 1);
                        leanh::lean_dec(v_unused_2161_);
                        v_unused_2162_ = leanh::lean_ctor_get(v_r_1943_, 0);
                        leanh::lean_dec(v_unused_2162_);
                        v___x_2121_ = v_r_1943_;
                        v_isShared_2122_ = v_isSharedCheck_2157_;
                        state = 54;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1943_);
                        v___x_2121_ = leanh::lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2157_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_2163_ = lean_nat_add(v___x_1949_, v_size_1939_);
                    leanh::lean_dec(v_size_1939_);
                    v___x_2164_ = lean_nat_add(v___x_2163_, v_size_2099_);
                    leanh::lean_dec(v___x_2163_);
                    v___x_2165_ = lean_nat_add(v___x_1949_, v_size_2099_);
                    v___x_2166_ = lean_nat_add(v___x_2165_, v_size_2112_);
                    leanh::lean_dec(v___x_2165_);
                    if v_isShared_2094_ == 0 {
                        leanh::lean_ctor_set(v___x_2093_, 4, v_tree_2096_);
                        leanh::lean_ctor_set(v___x_2093_, 3, v_r_1943_);
                        leanh::lean_ctor_set(v___x_2093_, 2, v_v_2098_);
                        leanh::lean_ctor_set(v___x_2093_, 1, v_k_2097_);
                        leanh::lean_ctor_set(v___x_2093_, 0, v___x_2166_);
                        v___x_2168_ = v___x_2093_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2166_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2097_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2098_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_1943_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_tree_2096_);
                        v___x_2168_ = v_reuseFailAlloc_2172_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_2123_ = lean_nat_add(v___x_1949_, v_size_1939_);
                leanh::lean_dec(v_size_1939_);
                v___x_2124_ = lean_nat_add(v___x_2123_, v_size_2099_);
                leanh::lean_dec(v___x_2123_);
                v___x_2145_ = lean_nat_add(v___x_1949_, v_size_2111_);
                if leanh::lean_obj_tag(v_l_2115_) == 0 {
                    v_size_2155_ = leanh::lean_ctor_get(v_l_2115_, 0);
                    leanh::lean_inc(v_size_2155_);
                    v___y_2147_ = v_size_2155_;
                    state = 59;
                    continue;
                } else {
                    v___x_2156_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2147_ = v___x_2156_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_2129_ = lean_nat_add(v___y_2126_, v___y_2128_);
                leanh::lean_dec(v___y_2128_);
                leanh::lean_dec(v___y_2126_);
                leanh::lean_inc_ref(v_tree_2096_);
                if v_isShared_2122_ == 0 {
                    leanh::lean_ctor_set(v___x_2121_, 4, v_tree_2096_);
                    leanh::lean_ctor_set(v___x_2121_, 3, v_r_2116_);
                    leanh::lean_ctor_set(v___x_2121_, 2, v_v_2098_);
                    leanh::lean_ctor_set(v___x_2121_, 1, v_k_2097_);
                    leanh::lean_ctor_set(v___x_2121_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2121_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2144_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_r_2116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_tree_2096_);
                    v___x_2131_ = v_reuseFailAlloc_2144_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_2138_ = (!leanh::lean_is_exclusive(v_tree_2096_)) as u8;
                if v_isSharedCheck_2138_ == 0 {
                    v_unused_2139_ = leanh::lean_ctor_get(v_tree_2096_, 4);
                    leanh::lean_dec(v_unused_2139_);
                    v_unused_2140_ = leanh::lean_ctor_get(v_tree_2096_, 3);
                    leanh::lean_dec(v_unused_2140_);
                    v_unused_2141_ = leanh::lean_ctor_get(v_tree_2096_, 2);
                    leanh::lean_dec(v_unused_2141_);
                    v_unused_2142_ = leanh::lean_ctor_get(v_tree_2096_, 1);
                    leanh::lean_dec(v_unused_2142_);
                    v_unused_2143_ = leanh::lean_ctor_get(v_tree_2096_, 0);
                    leanh::lean_dec(v_unused_2143_);
                    v___x_2133_ = v_tree_2096_;
                    v_isShared_2134_ = v_isSharedCheck_2138_;
                    state = 57;
                    continue;
                } else {
                    leanh::lean_dec(v_tree_2096_);
                    v___x_2133_ = leanh::lean_box(0);
                    v_isShared_2134_ = v_isSharedCheck_2138_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2134_ == 0 {
                    leanh::lean_ctor_set(v___x_2133_, 4, v___x_2131_);
                    leanh::lean_ctor_set(v___x_2133_, 3, v___y_2127_);
                    leanh::lean_ctor_set(v___x_2133_, 2, v_v_2114_);
                    leanh::lean_ctor_set(v___x_2133_, 1, v_k_2113_);
                    leanh::lean_ctor_set(v___x_2133_, 0, v___x_2124_);
                    v___x_2136_ = v___x_2133_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_2113_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_2114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 3, v___y_2127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 4, v___x_2131_);
                    v___x_2136_ = v_reuseFailAlloc_2137_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_2136_;
            }
            59 => {
                v___x_2148_ = lean_nat_add(v___x_2145_, v___y_2147_);
                leanh::lean_dec(v___y_2147_);
                leanh::lean_dec(v___x_2145_);
                if v_isShared_2094_ == 0 {
                    leanh::lean_ctor_set(v___x_2093_, 4, v_l_2115_);
                    leanh::lean_ctor_set(v___x_2093_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v___x_2093_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v___x_2093_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v___x_2093_, 0, v___x_2148_);
                    v___x_2150_ = v___x_2093_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_l_2115_);
                    v___x_2150_ = v_reuseFailAlloc_2154_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_2151_ = lean_nat_add(v___x_1949_, v_size_2099_);
                if leanh::lean_obj_tag(v_r_2116_) == 0 {
                    v_size_2152_ = leanh::lean_ctor_get(v_r_2116_, 0);
                    leanh::lean_inc(v_size_2152_);
                    v___y_2126_ = v___x_2151_;
                    v___y_2127_ = v___x_2150_;
                    v___y_2128_ = v_size_2152_;
                    state = 55;
                    continue;
                } else {
                    v___x_2153_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2126_ = v___x_2151_;
                    v___y_2127_ = v___x_2150_;
                    v___y_2128_ = v___x_2153_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_2110_ == 0 {
                    leanh::lean_ctor_set(v___x_2109_, 4, v___x_2168_);
                    leanh::lean_ctor_set(v___x_2109_, 0, v___x_2164_);
                    v___x_2170_ = v___x_2109_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2170_;
            }
            63 => {
                if leanh::lean_obj_tag(v_r_1943_) == 0 {
                    v_k_2182_ = leanh::lean_ctor_get(v___x_2095_, 0);
                    leanh::lean_inc(v_k_2182_);
                    v_v_2183_ = leanh::lean_ctor_get(v___x_2095_, 1);
                    leanh::lean_inc(v_v_2183_);
                    leanh::lean_dec_ref(v___x_2095_);
                    v_size_2184_ = leanh::lean_ctor_get(v_r_1943_, 0);
                    v___x_2185_ = lean_nat_add(v___x_1949_, v_size_1939_);
                    leanh::lean_dec(v_size_1939_);
                    v___x_2186_ = lean_nat_add(v___x_1949_, v_size_2184_);
                    if v_isShared_2094_ == 0 {
                        leanh::lean_ctor_set(v___x_2093_, 4, v_tree_2096_);
                        leanh::lean_ctor_set(v___x_2093_, 3, v_r_1943_);
                        leanh::lean_ctor_set(v___x_2093_, 2, v_v_2183_);
                        leanh::lean_ctor_set(v___x_2093_, 1, v_k_2182_);
                        leanh::lean_ctor_set(v___x_2093_, 0, v___x_2186_);
                        v___x_2188_ = v___x_2093_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2192_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2186_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_2182_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_2183_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_r_1943_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_tree_2096_);
                        v___x_2188_ = v_reuseFailAlloc_2192_;
                        state = 64;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_1939_);
                    v_k_2193_ = leanh::lean_ctor_get(v___x_2095_, 0);
                    leanh::lean_inc(v_k_2193_);
                    v_v_2194_ = leanh::lean_ctor_get(v___x_2095_, 1);
                    leanh::lean_inc(v_v_2194_);
                    leanh::lean_dec_ref(v___x_2095_);
                    v___x_2195_ = leanh::lean_unsigned_to_nat(3);
                    if v_isShared_2094_ == 0 {
                        leanh::lean_ctor_set(v___x_2093_, 4, v_r_1943_);
                        leanh::lean_ctor_set(v___x_2093_, 3, v_r_1943_);
                        leanh::lean_ctor_set(v___x_2093_, 2, v_v_2194_);
                        leanh::lean_ctor_set(v___x_2093_, 1, v_k_2193_);
                        leanh::lean_ctor_set(v___x_2093_, 0, v___x_1949_);
                        v___x_2197_ = v___x_2093_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_2201_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_1949_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2193_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2194_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_1943_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_r_1943_);
                        v___x_2197_ = v_reuseFailAlloc_2201_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_2181_ == 0 {
                    leanh::lean_ctor_set(v___x_2180_, 4, v___x_2188_);
                    leanh::lean_ctor_set(v___x_2180_, 0, v___x_2185_);
                    v___x_2190_ = v___x_2180_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 4, v___x_2188_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2190_;
            }
            66 => {
                if v_isShared_2181_ == 0 {
                    leanh::lean_ctor_set(v___x_2180_, 4, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2180_, 0, v___x_2195_);
                    v___x_2199_ = v___x_2180_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 4, v___x_2197_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2199_;
            }
            68 => {
                v_k_2211_ = leanh::lean_ctor_get(v___x_2095_, 0);
                leanh::lean_inc(v_k_2211_);
                v_v_2212_ = leanh::lean_ctor_get(v___x_2095_, 1);
                leanh::lean_inc(v_v_2212_);
                leanh::lean_dec_ref(v___x_2095_);
                v_k_2213_ = leanh::lean_ctor_get(v_r_1943_, 1);
                v_v_2214_ = leanh::lean_ctor_get(v_r_1943_, 2);
                v_isSharedCheck_2228_ = (!leanh::lean_is_exclusive(v_r_1943_)) as u8;
                if v_isSharedCheck_2228_ == 0 {
                    v_unused_2229_ = leanh::lean_ctor_get(v_r_1943_, 4);
                    leanh::lean_dec(v_unused_2229_);
                    v_unused_2230_ = leanh::lean_ctor_get(v_r_1943_, 3);
                    leanh::lean_dec(v_unused_2230_);
                    v_unused_2231_ = leanh::lean_ctor_get(v_r_1943_, 0);
                    leanh::lean_dec(v_unused_2231_);
                    v___x_2216_ = v_r_1943_;
                    v_isShared_2217_ = v_isSharedCheck_2228_;
                    state = 69;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2214_);
                    leanh::lean_inc(v_k_2213_);
                    leanh::lean_dec(v_r_1943_);
                    v___x_2216_ = leanh::lean_box(0);
                    v_isShared_2217_ = v_isSharedCheck_2228_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_2218_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2217_ == 0 {
                    leanh::lean_ctor_set(v___x_2216_, 4, v_l_1942_);
                    leanh::lean_ctor_set(v___x_2216_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v___x_2216_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v___x_2216_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v___x_2216_, 0, v___x_1949_);
                    v___x_2220_ = v___x_2216_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_1940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_l_1942_);
                    v___x_2220_ = v_reuseFailAlloc_2227_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2094_ == 0 {
                    leanh::lean_ctor_set(v___x_2093_, 4, v_l_1942_);
                    leanh::lean_ctor_set(v___x_2093_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v___x_2093_, 2, v_v_2212_);
                    leanh::lean_ctor_set(v___x_2093_, 1, v_k_2211_);
                    leanh::lean_ctor_set(v___x_2093_, 0, v___x_1949_);
                    v___x_2222_ = v___x_2093_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_l_1942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_l_1942_);
                    v___x_2222_ = v_reuseFailAlloc_2226_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_2210_ == 0 {
                    leanh::lean_ctor_set(v___x_2209_, 4, v___x_2222_);
                    leanh::lean_ctor_set(v___x_2209_, 3, v___x_2220_);
                    leanh::lean_ctor_set(v___x_2209_, 2, v_v_2214_);
                    leanh::lean_ctor_set(v___x_2209_, 1, v_k_2213_);
                    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2218_);
                    v___x_2224_ = v___x_2209_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_k_2213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_v_2214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 3, v___x_2220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 4, v___x_2222_);
                    v___x_2224_ = v_reuseFailAlloc_2225_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_2224_;
            }
            73 => {
                return v___x_2242_;
            }
            74 => {
                return v___x_2264_;
            }
            75 => {
                v_size_2269_ = leanh::lean_ctor_get(v_l_2256_, 0);
                v_size_2270_ = leanh::lean_ctor_get(v_r_2257_, 0);
                v_k_2271_ = leanh::lean_ctor_get(v_r_2257_, 1);
                v_v_2272_ = leanh::lean_ctor_get(v_r_2257_, 2);
                v_l_2273_ = leanh::lean_ctor_get(v_r_2257_, 3);
                v_r_2274_ = leanh::lean_ctor_get(v_r_2257_, 4);
                v___x_2275_ = leanh::lean_unsigned_to_nat(2);
                v___x_2276_ = lean_nat_mul(v___x_2275_, v_size_2269_);
                v___x_2277_ = lean_nat_dec_lt(v_size_2270_, v___x_2276_);
                leanh::lean_dec(v___x_2276_);
                if v___x_2277_ == 0 {
                    leanh::lean_inc(v_r_2274_);
                    leanh::lean_inc(v_l_2273_);
                    leanh::lean_inc(v_v_2272_);
                    leanh::lean_inc(v_k_2271_);
                    v_isSharedCheck_2306_ = (!leanh::lean_is_exclusive(v_r_2257_)) as u8;
                    if v_isSharedCheck_2306_ == 0 {
                        v_unused_2307_ = leanh::lean_ctor_get(v_r_2257_, 4);
                        leanh::lean_dec(v_unused_2307_);
                        v_unused_2308_ = leanh::lean_ctor_get(v_r_2257_, 3);
                        leanh::lean_dec(v_unused_2308_);
                        v_unused_2309_ = leanh::lean_ctor_get(v_r_2257_, 2);
                        leanh::lean_dec(v_unused_2309_);
                        v_unused_2310_ = leanh::lean_ctor_get(v_r_2257_, 1);
                        leanh::lean_dec(v_unused_2310_);
                        v_unused_2311_ = leanh::lean_ctor_get(v_r_2257_, 0);
                        leanh::lean_dec(v_unused_2311_);
                        v___x_2279_ = v_r_2257_;
                        v_isShared_2280_ = v_isSharedCheck_2306_;
                        state = 76;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2257_);
                        v___x_2279_ = leanh::lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2306_;
                        state = 76;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1762_);
                    v___x_2312_ = lean_nat_add(v___x_2251_, v_size_2253_);
                    leanh::lean_dec(v_size_2253_);
                    v___x_2313_ = lean_nat_add(v___x_2312_, v_size_2252_);
                    leanh::lean_dec(v___x_2312_);
                    v___x_2314_ = lean_nat_add(v___x_2251_, v_size_2252_);
                    leanh::lean_dec(v_size_2252_);
                    v___x_2315_ = lean_nat_add(v___x_2314_, v_size_2270_);
                    leanh::lean_dec(v___x_2314_);
                    leanh::lean_inc_ref(v_impl_2250_);
                    if v_isShared_2268_ == 0 {
                        leanh::lean_ctor_set(v___x_2267_, 4, v_impl_2250_);
                        leanh::lean_ctor_set(v___x_2267_, 3, v_r_2257_);
                        leanh::lean_ctor_set(v___x_2267_, 2, v_v_1758_);
                        leanh::lean_ctor_set(v___x_2267_, 1, v_k_1757_);
                        leanh::lean_ctor_set(v___x_2267_, 0, v___x_2315_);
                        v___x_2317_ = v___x_2267_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_2330_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2315_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_1757_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_1758_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_r_2257_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_impl_2250_);
                        v___x_2317_ = v_reuseFailAlloc_2330_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_2281_ = lean_nat_add(v___x_2251_, v_size_2253_);
                leanh::lean_dec(v_size_2253_);
                v___x_2282_ = lean_nat_add(v___x_2281_, v_size_2252_);
                leanh::lean_dec(v___x_2281_);
                v___x_2294_ = lean_nat_add(v___x_2251_, v_size_2269_);
                if leanh::lean_obj_tag(v_l_2273_) == 0 {
                    v_size_2304_ = leanh::lean_ctor_get(v_l_2273_, 0);
                    leanh::lean_inc(v_size_2304_);
                    v___y_2296_ = v_size_2304_;
                    state = 80;
                    continue;
                } else {
                    v___x_2305_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2296_ = v___x_2305_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_2287_ = lean_nat_add(v___y_2284_, v___y_2286_);
                leanh::lean_dec(v___y_2286_);
                leanh::lean_dec(v___y_2284_);
                if v_isShared_2280_ == 0 {
                    leanh::lean_ctor_set(v___x_2279_, 4, v_impl_2250_);
                    leanh::lean_ctor_set(v___x_2279_, 3, v_r_2274_);
                    leanh::lean_ctor_set(v___x_2279_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_2279_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2287_);
                    v___x_2289_ = v___x_2279_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_r_2274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_impl_2250_);
                    v___x_2289_ = v_reuseFailAlloc_2293_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_2268_ == 0 {
                    leanh::lean_ctor_set(v___x_2267_, 4, v___x_2289_);
                    leanh::lean_ctor_set(v___x_2267_, 3, v___y_2285_);
                    leanh::lean_ctor_set(v___x_2267_, 2, v_v_2272_);
                    leanh::lean_ctor_set(v___x_2267_, 1, v_k_2271_);
                    leanh::lean_ctor_set(v___x_2267_, 0, v___x_2282_);
                    v___x_2291_ = v___x_2267_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2292_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 3, v___y_2285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2292_, 4, v___x_2289_);
                    v___x_2291_ = v_reuseFailAlloc_2292_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_2291_;
            }
            80 => {
                v___x_2297_ = lean_nat_add(v___x_2294_, v___y_2296_);
                leanh::lean_dec(v___y_2296_);
                leanh::lean_dec(v___x_2294_);
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v_l_2273_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v_l_2256_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_2255_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_2254_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_2297_);
                    v___x_2299_ = v___x_1762_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_2303_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_k_2254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_v_2255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 3, v_l_2256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 4, v_l_2273_);
                    v___x_2299_ = v_reuseFailAlloc_2303_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_2300_ = lean_nat_add(v___x_2251_, v_size_2252_);
                leanh::lean_dec(v_size_2252_);
                if leanh::lean_obj_tag(v_r_2274_) == 0 {
                    v_size_2301_ = leanh::lean_ctor_get(v_r_2274_, 0);
                    leanh::lean_inc(v_size_2301_);
                    v___y_2284_ = v___x_2300_;
                    v___y_2285_ = v___x_2299_;
                    v___y_2286_ = v_size_2301_;
                    state = 77;
                    continue;
                } else {
                    v___x_2302_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2284_ = v___x_2300_;
                    v___y_2285_ = v___x_2299_;
                    v___y_2286_ = v___x_2302_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_2324_ = (!leanh::lean_is_exclusive(v_impl_2250_)) as u8;
                if v_isSharedCheck_2324_ == 0 {
                    v_unused_2325_ = leanh::lean_ctor_get(v_impl_2250_, 4);
                    leanh::lean_dec(v_unused_2325_);
                    v_unused_2326_ = leanh::lean_ctor_get(v_impl_2250_, 3);
                    leanh::lean_dec(v_unused_2326_);
                    v_unused_2327_ = leanh::lean_ctor_get(v_impl_2250_, 2);
                    leanh::lean_dec(v_unused_2327_);
                    v_unused_2328_ = leanh::lean_ctor_get(v_impl_2250_, 1);
                    leanh::lean_dec(v_unused_2328_);
                    v_unused_2329_ = leanh::lean_ctor_get(v_impl_2250_, 0);
                    leanh::lean_dec(v_unused_2329_);
                    v___x_2319_ = v_impl_2250_;
                    v_isShared_2320_ = v_isSharedCheck_2324_;
                    state = 83;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_2250_);
                    v___x_2319_ = leanh::lean_box(0);
                    v_isShared_2320_ = v_isSharedCheck_2324_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_2320_ == 0 {
                    leanh::lean_ctor_set(v___x_2319_, 4, v___x_2317_);
                    leanh::lean_ctor_set(v___x_2319_, 3, v_l_2256_);
                    leanh::lean_ctor_set(v___x_2319_, 2, v_v_2255_);
                    leanh::lean_ctor_set(v___x_2319_, 1, v_k_2254_);
                    leanh::lean_ctor_set(v___x_2319_, 0, v___x_2313_);
                    v___x_2322_ = v___x_2319_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_2323_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_k_2254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_v_2255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_l_2256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 4, v___x_2317_);
                    v___x_2322_ = v_reuseFailAlloc_2323_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_2322_;
            }
            85 => {
                return v___x_2340_;
            }
            86 => {
                v_size_2350_ = leanh::lean_ctor_get(v_r_2343_, 0);
                v___x_2351_ = lean_nat_add(v___x_2251_, v_size_2344_);
                leanh::lean_dec(v_size_2344_);
                v___x_2352_ = lean_nat_add(v___x_2251_, v_size_2350_);
                if v_isShared_2349_ == 0 {
                    leanh::lean_ctor_set(v___x_2348_, 4, v_impl_2250_);
                    leanh::lean_ctor_set(v___x_2348_, 3, v_r_2343_);
                    leanh::lean_ctor_set(v___x_2348_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_2348_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_2348_, 0, v___x_2352_);
                    v___x_2354_ = v___x_2348_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_r_2343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_impl_2250_);
                    v___x_2354_ = v_reuseFailAlloc_2358_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v___x_2354_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_2346_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_2345_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_2351_);
                    v___x_2356_ = v___x_1762_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2345_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 4, v___x_2354_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_2356_;
            }
            89 => {
                v___x_2367_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2366_ == 0 {
                    leanh::lean_ctor_set(v___x_2365_, 3, v_r_2343_);
                    leanh::lean_ctor_set(v___x_2365_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_2365_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_2365_, 0, v___x_2251_);
                    v___x_2369_ = v___x_2365_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_r_2343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_r_2343_);
                    v___x_2369_ = v_reuseFailAlloc_2373_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v___x_2369_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_2363_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_2362_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_2367_);
                    v___x_2371_ = v___x_1762_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_2372_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2367_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_k_2362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_v_2363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 4, v___x_2369_);
                    v___x_2371_ = v_reuseFailAlloc_2372_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_2371_;
            }
            92 => {
                v_k_2384_ = leanh::lean_ctor_get(v_r_2378_, 1);
                v_v_2385_ = leanh::lean_ctor_get(v_r_2378_, 2);
                v_isSharedCheck_2399_ = (!leanh::lean_is_exclusive(v_r_2378_)) as u8;
                if v_isSharedCheck_2399_ == 0 {
                    v_unused_2400_ = leanh::lean_ctor_get(v_r_2378_, 4);
                    leanh::lean_dec(v_unused_2400_);
                    v_unused_2401_ = leanh::lean_ctor_get(v_r_2378_, 3);
                    leanh::lean_dec(v_unused_2401_);
                    v_unused_2402_ = leanh::lean_ctor_get(v_r_2378_, 0);
                    leanh::lean_dec(v_unused_2402_);
                    v___x_2387_ = v_r_2378_;
                    v_isShared_2388_ = v_isSharedCheck_2399_;
                    state = 93;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2385_);
                    leanh::lean_inc(v_k_2384_);
                    leanh::lean_dec(v_r_2378_);
                    v___x_2387_ = leanh::lean_box(0);
                    v_isShared_2388_ = v_isSharedCheck_2399_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_2389_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2388_ == 0 {
                    leanh::lean_ctor_set(v___x_2387_, 4, v_l_2342_);
                    leanh::lean_ctor_set(v___x_2387_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v___x_2387_, 2, v_v_2380_);
                    leanh::lean_ctor_set(v___x_2387_, 1, v_k_2379_);
                    leanh::lean_ctor_set(v___x_2387_, 0, v___x_2251_);
                    v___x_2391_ = v___x_2387_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_l_2342_);
                    v___x_2391_ = v_reuseFailAlloc_2398_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_2383_ == 0 {
                    leanh::lean_ctor_set(v___x_2382_, 4, v_l_2342_);
                    leanh::lean_ctor_set(v___x_2382_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v___x_2382_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v___x_2382_, 0, v___x_2251_);
                    v___x_2393_ = v___x_2382_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_l_2342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_l_2342_);
                    v___x_2393_ = v_reuseFailAlloc_2397_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 4, v___x_2393_);
                    leanh::lean_ctor_set(v___x_1762_, 3, v___x_2391_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_v_2385_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_k_2384_);
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_2389_);
                    v___x_2395_ = v___x_1762_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_2396_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2389_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_k_2384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_v_2385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 3, v___x_2391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 4, v___x_2393_);
                    v___x_2395_ = v_reuseFailAlloc_2396_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_2395_;
            }
            97 => {
                return v___x_2409_;
            }
            98 => {
                return v___x_2412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg___boxed(
    mut v_k_2416_: *mut leanh::LeanObject,
    mut v_t_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_k_2416_, v_t_2417_);
    leanh::lean_dec(v_k_2416_);
    return v_res_2418_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(
    mut v_name_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2422_ = lean_st_ref_get(v_a_2420_);
                v_remaining_2423_ = leanh::lean_ctor_get(v___x_2422_, 1);
                leanh::lean_inc(v_remaining_2423_);
                leanh::lean_dec(v___x_2422_);
                v___x_2424_ = l_Lean_NameSet_contains(v_remaining_2423_, v_name_2419_);
                leanh::lean_dec(v_remaining_2423_);
                if v___x_2424_ == 0 {
                    leanh::lean_dec(v_name_2419_);
                    v___x_2425_ = leanh::lean_box((v___x_2424_) as usize);
                    v___x_2426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2426_, 0, v___x_2425_);
                    return v___x_2426_;
                } else {
                    v___x_2427_ = lean_st_ref_take(v_a_2420_);
                    v_env_2428_ = leanh::lean_ctor_get(v___x_2427_, 0);
                    v_remaining_2429_ = leanh::lean_ctor_get(v___x_2427_, 1);
                    v_pending_2430_ = leanh::lean_ctor_get(v___x_2427_, 2);
                    v_postponedConstructors_2431_ = leanh::lean_ctor_get(v___x_2427_, 3);
                    v_postponedRecursors_2432_ = leanh::lean_ctor_get(v___x_2427_, 4);
                    v_isSharedCheck_2444_ = (!leanh::lean_is_exclusive(v___x_2427_)) as u8;
                    if v_isSharedCheck_2444_ == 0 {
                        v___x_2434_ = v___x_2427_;
                        v_isShared_2435_ = v_isSharedCheck_2444_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_postponedRecursors_2432_);
                        leanh::lean_inc(v_postponedConstructors_2431_);
                        leanh::lean_inc(v_pending_2430_);
                        leanh::lean_inc(v_remaining_2429_);
                        leanh::lean_inc(v_env_2428_);
                        leanh::lean_dec(v___x_2427_);
                        v___x_2434_ = leanh::lean_box(0);
                        v_isShared_2435_ = v_isSharedCheck_2444_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2436_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_name_2419_, v_remaining_2429_);
                v___x_2437_ = l_Lean_NameSet_insert(v_pending_2430_, v_name_2419_);
                if v_isShared_2435_ == 0 {
                    leanh::lean_ctor_set(v___x_2434_, 2, v___x_2437_);
                    leanh::lean_ctor_set(v___x_2434_, 1, v___x_2436_);
                    v___x_2439_ = v___x_2434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2443_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_env_2428_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 2, v___x_2437_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2443_,
                        3,
                        v_postponedConstructors_2431_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2443_,
                        4,
                        v_postponedRecursors_2432_,
                    );
                    v___x_2439_ = v_reuseFailAlloc_2443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2440_ = lean_st_ref_set(v_a_2420_, v___x_2439_);
                v___x_2441_ = leanh::lean_box((v___x_2424_) as usize);
                v___x_2442_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2442_, 0, v___x_2441_);
                return v___x_2442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg___boxed(
    mut v_name_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2448_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(v_name_2445_, v_a_2446_);
    leanh::lean_dec(v_a_2446_);
    return v_res_2448_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo(
    mut v_name_2449_: *mut leanh::LeanObject,
    mut v_a_2450_: *mut leanh::LeanObject,
    mut v_a_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(v_name_2449_, v_a_2451_);
    return v___x_2453_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___boxed(
    mut v_name_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
    mut v_a_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo(
        v_name_2454_,
        v_a_2455_,
        v_a_2456_,
    );
    leanh::lean_dec(v_a_2456_);
    leanh::lean_dec_ref(v_a_2455_);
    return v_res_2458_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0(
    mut v_00_u03b2_2459_: *mut leanh::LeanObject,
    mut v_k_2460_: *mut leanh::LeanObject,
    mut v_t_2461_: *mut leanh::LeanObject,
    mut v_h_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_k_2460_, v_t_2461_);
    return v___x_2463_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___boxed(
    mut v_00_u03b2_2464_: *mut leanh::LeanObject,
    mut v_k_2465_: *mut leanh::LeanObject,
    mut v_t_2466_: *mut leanh::LeanObject,
    mut v_h_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0(v_00_u03b2_2464_, v_k_2465_, v_t_2466_, v_h_2467_);
    leanh::lean_dec(v_k_2465_);
    return v_res_2468_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(
    mut v_ex_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = l_Lean_Options_empty;
    v___x_2472_ = l_Lean_Kernel_Exception_toMessageData(v_ex_2469_, v___x_2471_);
    v___x_2473_ = l_Lean_MessageData_toString(v___x_2472_);
    v___x_2474_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    v___x_2475_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2475_, 0, v___x_2474_);
    return v___x_2475_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg___boxed(
    mut v_ex_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(
        v_ex_2476_,
    );
    return v_res_2478_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException(
    mut v_ex_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(
        v_ex_2479_,
    );
    return v___x_2483_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___boxed(
    mut v_ex_2484_: *mut leanh::LeanObject,
    mut v_a_2485_: *mut leanh::LeanObject,
    mut v_a_2486_: *mut leanh::LeanObject,
    mut v_a_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException(
        v_ex_2484_, v_a_2485_, v_a_2486_,
    );
    leanh::lean_dec(v_a_2486_);
    leanh::lean_dec_ref(v_a_2485_);
    return v_res_2488_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
    mut v_d_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: usize = 0;
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v_unused_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2492_ = lean_st_ref_get(v_a_2490_);
                v_env_2493_ = leanh::lean_ctor_get(v___x_2492_, 0);
                leanh::lean_inc_ref(v_env_2493_);
                leanh::lean_dec(v___x_2492_);
                v___x_2494_ = 0usize;
                v___x_2495_ = leanh::lean_box(0);
                v___x_2496_ = lean_add_decl(v_env_2493_, v___x_2494_, v_d_2489_, v___x_2495_);
                if leanh::lean_obj_tag(v___x_2496_) == 0 {
                    v_a_2497_ = leanh::lean_ctor_get(v___x_2496_, 0);
                    leanh::lean_inc(v_a_2497_);
                    leanh::lean_dec_ref_known(v___x_2496_, 1);
                    v___x_2498_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(v_a_2497_);
                    return v___x_2498_;
                } else {
                    v_a_2499_ = leanh::lean_ctor_get(v___x_2496_, 0);
                    v_isSharedCheck_2521_ = (!leanh::lean_is_exclusive(v___x_2496_)) as u8;
                    if v_isSharedCheck_2521_ == 0 {
                        v___x_2501_ = v___x_2496_;
                        v_isShared_2502_ = v_isSharedCheck_2521_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2499_);
                        leanh::lean_dec(v___x_2496_);
                        v___x_2501_ = leanh::lean_box(0);
                        v_isShared_2502_ = v_isSharedCheck_2521_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2503_ = lean_st_ref_take(v_a_2490_);
                v_remaining_2504_ = leanh::lean_ctor_get(v___x_2503_, 1);
                v_pending_2505_ = leanh::lean_ctor_get(v___x_2503_, 2);
                v_postponedConstructors_2506_ = leanh::lean_ctor_get(v___x_2503_, 3);
                v_postponedRecursors_2507_ = leanh::lean_ctor_get(v___x_2503_, 4);
                v_isSharedCheck_2519_ = (!leanh::lean_is_exclusive(v___x_2503_)) as u8;
                if v_isSharedCheck_2519_ == 0 {
                    v_unused_2520_ = leanh::lean_ctor_get(v___x_2503_, 0);
                    leanh::lean_dec(v_unused_2520_);
                    v___x_2509_ = v___x_2503_;
                    v_isShared_2510_ = v_isSharedCheck_2519_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_postponedRecursors_2507_);
                    leanh::lean_inc(v_postponedConstructors_2506_);
                    leanh::lean_inc(v_pending_2505_);
                    leanh::lean_inc(v_remaining_2504_);
                    leanh::lean_dec(v___x_2503_);
                    v___x_2509_ = leanh::lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2510_ == 0 {
                    leanh::lean_ctor_set(v___x_2509_, 0, v_a_2499_);
                    v___x_2512_ = v___x_2509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_remaining_2504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_pending_2505_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2518_,
                        3,
                        v_postponedConstructors_2506_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2518_,
                        4,
                        v_postponedRecursors_2507_,
                    );
                    v___x_2512_ = v_reuseFailAlloc_2518_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2513_ = lean_st_ref_set(v_a_2490_, v___x_2512_);
                v___x_2514_ = leanh::lean_box(0);
                if v_isShared_2502_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2501_, 0);
                    leanh::lean_ctor_set(v___x_2501_, 0, v___x_2514_);
                    v___x_2516_ = v___x_2501_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
                    v___x_2516_ = v_reuseFailAlloc_2517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg___boxed(
    mut v_d_2522_: *mut leanh::LeanObject,
    mut v_a_2523_: *mut leanh::LeanObject,
    mut v_a_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v_d_2522_, v_a_2523_);
    leanh::lean_dec(v_a_2523_);
    leanh::lean_dec(v_d_2522_);
    return v_res_2525_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl(
    mut v_d_2526_: *mut leanh::LeanObject,
    mut v_a_2527_: *mut leanh::LeanObject,
    mut v_a_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v_d_2526_, v_a_2528_);
    return v___x_2530_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___boxed(
    mut v_d_2531_: *mut leanh::LeanObject,
    mut v_a_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
    mut v_a_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2535_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl(v_d_2531_, v_a_2532_, v_a_2533_);
    leanh::lean_dec(v_a_2533_);
    leanh::lean_dec_ref(v_a_2532_);
    leanh::lean_dec(v_d_2531_);
    return v_res_2535_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2536_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2536_;
}
pub unsafe fn l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10(
    mut v_msg_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_32059__overap_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0_once), _init_l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0);
    v___x_2542_ = l_StateRefT_x27_instMonad___redArg(v___x_2541_);
    v___x_2543_ = leanh::lean_box(0);
    v___x_2544_ = l_instInhabitedOfMonad___redArg(v___x_2542_, v___x_2543_);
    v___f_2545_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2545_, 0, v___x_2544_);
    v___x_32059__overap_2546_ = lean_panic_fn_borrowed(v___f_2545_, v_msg_2537_);
    leanh::lean_dec_ref(v___f_2545_);
    leanh::lean_inc(v___y_2539_);
    leanh::lean_inc_ref(v___y_2538_);
    v___x_2547_ = leanh::lean_apply_3(
        v___x_32059__overap_2546_,
        v___y_2538_,
        v___y_2539_,
        leanh::lean_box(0),
    );
    return v___x_2547_;
}
pub unsafe fn l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___boxed(
    mut v_msg_2548_: *mut leanh::LeanObject,
    mut v___y_2549_: *mut leanh::LeanObject,
    mut v___y_2550_: *mut leanh::LeanObject,
    mut v___y_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2552_ =
        l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10(
            v_msg_2548_,
            v___y_2549_,
            v___y_2550_,
        );
    leanh::lean_dec(v___y_2550_);
    leanh::lean_dec_ref(v___y_2549_);
    return v_res_2552_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
    mut v_name_2555_: *mut leanh::LeanObject,
    mut v_____r_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
    mut v___y_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2568_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2560_ = lean_st_ref_take(v___y_2558_);
                v_env_2561_ = leanh::lean_ctor_get(v___x_2560_, 0);
                v_remaining_2562_ = leanh::lean_ctor_get(v___x_2560_, 1);
                v_pending_2563_ = leanh::lean_ctor_get(v___x_2560_, 2);
                v_postponedConstructors_2564_ = leanh::lean_ctor_get(v___x_2560_, 3);
                v_postponedRecursors_2565_ = leanh::lean_ctor_get(v___x_2560_, 4);
                v_isSharedCheck_2576_ = (!leanh::lean_is_exclusive(v___x_2560_)) as u8;
                if v_isSharedCheck_2576_ == 0 {
                    v___x_2567_ = v___x_2560_;
                    v_isShared_2568_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_postponedRecursors_2565_);
                    leanh::lean_inc(v_postponedConstructors_2564_);
                    leanh::lean_inc(v_pending_2563_);
                    leanh::lean_inc(v_remaining_2562_);
                    leanh::lean_inc(v_env_2561_);
                    leanh::lean_dec(v___x_2560_);
                    v___x_2567_ = leanh::lean_box(0);
                    v_isShared_2568_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2569_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_name_2555_, v_pending_2563_);
                if v_isShared_2568_ == 0 {
                    leanh::lean_ctor_set(v___x_2567_, 2, v___x_2569_);
                    v___x_2571_ = v___x_2567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_env_2561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_remaining_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 2, v___x_2569_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2575_,
                        3,
                        v_postponedConstructors_2564_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2575_,
                        4,
                        v_postponedRecursors_2565_,
                    );
                    v___x_2571_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2572_ = lean_st_ref_set(v___y_2558_, v___x_2571_);
                v___x_2573_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0;
                v___x_2574_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2574_, 0, v___x_2573_);
                return v___x_2574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___boxed(
    mut v_name_2577_: *mut leanh::LeanObject,
    mut v_____r_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
    mut v___y_2580_: *mut leanh::LeanObject,
    mut v___y_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2582_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
        v_name_2577_,
        v_____r_2578_,
        v___y_2579_,
        v___y_2580_,
    );
    leanh::lean_dec(v___y_2580_);
    leanh::lean_dec_ref(v___y_2579_);
    leanh::lean_dec(v_name_2577_);
    return v_res_2582_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1(
    mut v_val_2583_: *mut leanh::LeanObject,
    mut v___f_2584_: *mut leanh::LeanObject,
    mut v_____r_2585_: *mut leanh::LeanObject,
    mut v___y_2586_: *mut leanh::LeanObject,
    mut v___y_2587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2589_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2589_, 0, v_val_2583_);
                v___x_2590_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
                    v___x_2589_,
                    v___y_2587_,
                );
                leanh::lean_dec_ref_known(v___x_2589_, 1);
                if leanh::lean_obj_tag(v___x_2590_) == 0 {
                    v_a_2591_ = leanh::lean_ctor_get(v___x_2590_, 0);
                    leanh::lean_inc(v_a_2591_);
                    leanh::lean_dec_ref_known(v___x_2590_, 1);
                    leanh::lean_inc(v___y_2587_);
                    leanh::lean_inc_ref(v___y_2586_);
                    v___x_2592_ = leanh::lean_apply_4(
                        v___f_2584_,
                        v_a_2591_,
                        v___y_2586_,
                        v___y_2587_,
                        leanh::lean_box(0),
                    );
                    return v___x_2592_;
                } else {
                    leanh::lean_dec_ref(v___f_2584_);
                    v_a_2593_ = leanh::lean_ctor_get(v___x_2590_, 0);
                    v_isSharedCheck_2600_ = (!leanh::lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2595_ = v___x_2590_;
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2593_);
                        leanh::lean_dec(v___x_2590_);
                        v___x_2595_ = leanh::lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2596_ == 0 {
                    v___x_2598_ = v___x_2595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1___boxed(
    mut v_val_2601_: *mut leanh::LeanObject,
    mut v___f_2602_: *mut leanh::LeanObject,
    mut v_____r_2603_: *mut leanh::LeanObject,
    mut v___y_2604_: *mut leanh::LeanObject,
    mut v___y_2605_: *mut leanh::LeanObject,
    mut v___y_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1(
        v_val_2601_,
        v___f_2602_,
        v_____r_2603_,
        v___y_2604_,
        v___y_2605_,
    );
    leanh::lean_dec(v___y_2605_);
    leanh::lean_dec_ref(v___y_2604_);
    return v_res_2607_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(
    mut v___f_2608_: *mut leanh::LeanObject,
    mut v_x_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
    mut v___y_2611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = leanh::lean_box(0);
    leanh::lean_inc(v___y_2611_);
    leanh::lean_inc_ref(v___y_2610_);
    v___x_2614_ = leanh::lean_apply_4(
        v___f_2608_,
        v___x_2613_,
        v___y_2610_,
        v___y_2611_,
        leanh::lean_box(0),
    );
    return v___x_2614_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2___boxed(
    mut v___f_2615_: *mut leanh::LeanObject,
    mut v_x_2616_: *mut leanh::LeanObject,
    mut v___y_2617_: *mut leanh::LeanObject,
    mut v___y_2618_: *mut leanh::LeanObject,
    mut v___y_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(
        v___f_2615_,
        v_x_2616_,
        v___y_2617_,
        v___y_2618_,
    );
    leanh::lean_dec(v___y_2618_);
    leanh::lean_dec_ref(v___y_2617_);
    leanh::lean_dec(v_x_2616_);
    return v_res_2620_;
}
pub unsafe fn l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(
    mut v_x_2621_: *mut leanh::LeanObject,
    mut v_x_2622_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: u8 = 0;
    let mut v_head_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2621_) == 0 {
                    if leanh::lean_obj_tag(v_x_2622_) == 0 {
                        v___x_2623_ = 1;
                        return v___x_2623_;
                    } else {
                        v___x_2624_ = 0;
                        return v___x_2624_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_2622_) == 0 {
                        v___x_2625_ = 0;
                        return v___x_2625_;
                    } else {
                        v_head_2626_ = leanh::lean_ctor_get(v_x_2621_, 0);
                        v_tail_2627_ = leanh::lean_ctor_get(v_x_2621_, 1);
                        v_head_2628_ = leanh::lean_ctor_get(v_x_2622_, 0);
                        v_tail_2629_ = leanh::lean_ctor_get(v_x_2622_, 1);
                        v___x_2630_ = lean_name_eq(v_head_2626_, v_head_2628_);
                        if v___x_2630_ == 0 {
                            return v___x_2630_;
                        } else {
                            v_x_2621_ = v_tail_2627_;
                            v_x_2622_ = v_tail_2629_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4___boxed(
    mut v_x_2632_: *mut leanh::LeanObject,
    mut v_x_2633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2634_: u8 = 0;
    let mut v_r_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2634_ =
        l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(
            v_x_2632_, v_x_2633_,
        );
    leanh::lean_dec(v_x_2633_);
    leanh::lean_dec(v_x_2632_);
    v_r_2635_ = leanh::lean_box((v_res_2634_) as usize);
    return v_r_2635_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(
    mut v_msg_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2637_ = l_Lean_instInhabitedConstantInfo_default;
    v___x_2638_ = lean_panic_fn_borrowed(v___x_2637_, v_msg_2636_);
    return v___x_2638_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2;
    v___x_2643_ = leanh::lean_unsigned_to_nat(11);
    v___x_2644_ = leanh::lean_unsigned_to_nat(163);
    v___x_2645_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1;
    v___x_2646_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0;
    v___x_2647_ = l_mkPanicMessageWithDecl(
        v___x_2646_,
        v___x_2645_,
        v___x_2644_,
        v___x_2643_,
        v___x_2642_,
    );
    return v___x_2647_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0(
    mut v_a_2648_: *mut leanh::LeanObject,
    mut v_x_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2649_) == 0 {
                    v___x_2650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3);
                    v___x_2651_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(v___x_2650_);
                    return v___x_2651_;
                } else {
                    v_key_2652_ = leanh::lean_ctor_get(v_x_2649_, 0);
                    v_value_2653_ = leanh::lean_ctor_get(v_x_2649_, 1);
                    v_tail_2654_ = leanh::lean_ctor_get(v_x_2649_, 2);
                    v___x_2655_ = lean_name_eq(v_key_2652_, v_a_2648_);
                    if v___x_2655_ == 0 {
                        v_x_2649_ = v_tail_2654_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2653_);
                        return v_value_2653_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___boxed(
    mut v_a_2657_: *mut leanh::LeanObject,
    mut v_x_2658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2659_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0(v_a_2657_, v_x_2658_);
    leanh::lean_dec(v_x_2658_);
    leanh::lean_dec(v_a_2657_);
    return v_res_2659_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0()
-> u64 {
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: u64 = 0;
    v___x_2660_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2661_ = lean_uint64_of_nat(v___x_2660_);
    return v___x_2661_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0(
    mut v_m_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: u64 = 0;
    let mut v___x_2668_: u64 = 0;
    let mut v___x_2669_: u64 = 0;
    let mut v_fold_2670_: u64 = 0;
    let mut v___x_2671_: u64 = 0;
    let mut v___x_2672_: u64 = 0;
    let mut v___x_2673_: u64 = 0;
    let mut v___x_2674_: usize = 0;
    let mut v___x_2675_: usize = 0;
    let mut v___x_2676_: usize = 0;
    let mut v___x_2677_: usize = 0;
    let mut v___x_2678_: usize = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u64 = 0;
    let mut v_hash_2682_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2664_ = leanh::lean_ctor_get(v_m_2662_, 1);
                v___x_2665_ = lean_array_get_size(v_buckets_2664_);
                if leanh::lean_obj_tag(v_a_2663_) == 0 {
                    v___x_2681_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0);
                    v___y_2667_ = v___x_2681_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2682_ = leanh::lean_ctor_get_uint64(
                        v_a_2663_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2667_ = v_hash_2682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2668_ = 32u64;
                v___x_2669_ = lean_uint64_shift_right(v___y_2667_, v___x_2668_);
                v_fold_2670_ = lean_uint64_xor(v___y_2667_, v___x_2669_);
                v___x_2671_ = 16u64;
                v___x_2672_ = lean_uint64_shift_right(v_fold_2670_, v___x_2671_);
                v___x_2673_ = lean_uint64_xor(v_fold_2670_, v___x_2672_);
                v___x_2674_ = lean_uint64_to_usize(v___x_2673_);
                v___x_2675_ = lean_usize_of_nat(v___x_2665_);
                v___x_2676_ = 1usize;
                v___x_2677_ = lean_usize_sub(v___x_2675_, v___x_2676_);
                v___x_2678_ = lean_usize_land(v___x_2674_, v___x_2677_);
                v___x_2679_ = lean_array_uget_borrowed(v_buckets_2664_, v___x_2678_);
                v___x_2680_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0(v_a_2663_, v___x_2679_);
                return v___x_2680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___boxed(
    mut v_m_2683_: *mut leanh::LeanObject,
    mut v_a_2684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0(v_m_2683_, v_a_2684_);
    leanh::lean_dec(v_a_2684_);
    leanh::lean_dec_ref(v_m_2683_);
    return v_res_2685_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(
    mut v_x_2686_: *mut leanh::LeanObject,
    mut v_x_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2686_) == 0 {
                    v___x_2690_ = l_List_reverse___redArg(v_x_2687_);
                    v___x_2691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                    return v___x_2691_;
                } else {
                    v_head_2692_ = leanh::lean_ctor_get(v_x_2686_, 0);
                    v_tail_2693_ = leanh::lean_ctor_get(v_x_2686_, 1);
                    v_isSharedCheck_2702_ = (!leanh::lean_is_exclusive(v_x_2686_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2695_ = v_x_2686_;
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2693_);
                        leanh::lean_inc(v_head_2692_);
                        leanh::lean_dec(v_x_2686_);
                        v___x_2695_ = leanh::lean_box(0);
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0(v___y_2688_, v_head_2692_);
                leanh::lean_dec(v_head_2692_);
                if v_isShared_2696_ == 0 {
                    leanh::lean_ctor_set(v___x_2695_, 1, v_x_2687_);
                    leanh::lean_ctor_set(v___x_2695_, 0, v___x_2697_);
                    v___x_2699_ = v___x_2695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_x_2687_);
                    v___x_2699_ = v_reuseFailAlloc_2701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_2686_ = v_tail_2693_;
                v_x_2687_ = v___x_2699_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg___boxed(
    mut v_x_2703_: *mut leanh::LeanObject,
    mut v_x_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_x_2703_, v_x_2704_, v___y_2705_);
    leanh::lean_dec_ref(v___y_2705_);
    return v_res_2707_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7(
    mut v_x_2708_: *mut leanh::LeanObject,
    mut v_x_2709_: *mut leanh::LeanObject,
    mut v___y_2710_: *mut leanh::LeanObject,
    mut v___y_2711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2708_) == 0 {
                    v___x_2713_ = l_List_reverse___redArg(v_x_2709_);
                    v___x_2714_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2714_, 0, v___x_2713_);
                    return v___x_2714_;
                } else {
                    v_head_2715_ = leanh::lean_ctor_get(v_x_2708_, 0);
                    v_tail_2716_ = leanh::lean_ctor_get(v_x_2708_, 1);
                    v_isSharedCheck_2730_ = (!leanh::lean_is_exclusive(v_x_2708_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2718_ = v_x_2708_;
                        v_isShared_2719_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2716_);
                        leanh::lean_inc(v_head_2715_);
                        leanh::lean_dec(v_x_2708_);
                        v___x_2718_ = leanh::lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2720_ = l_Lean_ConstantInfo_inductiveVal_x21(v_head_2715_);
                v_ctors_2721_ = leanh::lean_ctor_get(v___x_2720_, 4);
                leanh::lean_inc(v_ctors_2721_);
                leanh::lean_dec_ref(v___x_2720_);
                v___x_2722_ = leanh::lean_box(0);
                v___x_2723_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_ctors_2721_, v___x_2722_, v___y_2710_);
                v_a_2724_ = leanh::lean_ctor_get(v___x_2723_, 0);
                leanh::lean_inc(v_a_2724_);
                leanh::lean_dec_ref(v___x_2723_);
                v___x_2725_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2725_, 0, v_head_2715_);
                leanh::lean_ctor_set(v___x_2725_, 1, v_a_2724_);
                if v_isShared_2719_ == 0 {
                    leanh::lean_ctor_set(v___x_2718_, 1, v_x_2709_);
                    leanh::lean_ctor_set(v___x_2718_, 0, v___x_2725_);
                    v___x_2727_ = v___x_2718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2725_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_x_2709_);
                    v___x_2727_ = v_reuseFailAlloc_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_2708_ = v_tail_2716_;
                v_x_2709_ = v___x_2727_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7___boxed(
    mut v_x_2731_: *mut leanh::LeanObject,
    mut v_x_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
    mut v___y_2734_: *mut leanh::LeanObject,
    mut v___y_2735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2736_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7(v_x_2731_, v_x_2732_, v___y_2733_, v___y_2734_);
    leanh::lean_dec(v___y_2734_);
    leanh::lean_dec_ref(v___y_2733_);
    return v_res_2736_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(
    mut v_a_2737_: *mut leanh::LeanObject,
    mut v_x_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2738_) == 0 {
                    v___x_2739_ = leanh::lean_box(0);
                    return v___x_2739_;
                } else {
                    v_key_2740_ = leanh::lean_ctor_get(v_x_2738_, 0);
                    v_value_2741_ = leanh::lean_ctor_get(v_x_2738_, 1);
                    v_tail_2742_ = leanh::lean_ctor_get(v_x_2738_, 2);
                    v___x_2743_ = lean_name_eq(v_key_2740_, v_a_2737_);
                    if v___x_2743_ == 0 {
                        v_x_2738_ = v_tail_2742_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2741_);
                        v___x_2745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2745_, 0, v_value_2741_);
                        return v___x_2745_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg___boxed(
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_x_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_2746_, v_x_2747_);
    leanh::lean_dec(v_x_2747_);
    leanh::lean_dec(v_a_2746_);
    return v_res_2748_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(
    mut v_m_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: u64 = 0;
    let mut v___x_2755_: u64 = 0;
    let mut v___x_2756_: u64 = 0;
    let mut v_fold_2757_: u64 = 0;
    let mut v___x_2758_: u64 = 0;
    let mut v___x_2759_: u64 = 0;
    let mut v___x_2760_: u64 = 0;
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u64 = 0;
    let mut v_hash_2769_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2751_ = leanh::lean_ctor_get(v_m_2749_, 1);
                v___x_2752_ = lean_array_get_size(v_buckets_2751_);
                if leanh::lean_obj_tag(v_a_2750_) == 0 {
                    v___x_2768_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0);
                    v___y_2754_ = v___x_2768_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2769_ = leanh::lean_ctor_get_uint64(
                        v_a_2750_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2754_ = v_hash_2769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2755_ = 32u64;
                v___x_2756_ = lean_uint64_shift_right(v___y_2754_, v___x_2755_);
                v_fold_2757_ = lean_uint64_xor(v___y_2754_, v___x_2756_);
                v___x_2758_ = 16u64;
                v___x_2759_ = lean_uint64_shift_right(v_fold_2757_, v___x_2758_);
                v___x_2760_ = lean_uint64_xor(v_fold_2757_, v___x_2759_);
                v___x_2761_ = lean_uint64_to_usize(v___x_2760_);
                v___x_2762_ = lean_usize_of_nat(v___x_2752_);
                v___x_2763_ = 1usize;
                v___x_2764_ = lean_usize_sub(v___x_2762_, v___x_2763_);
                v___x_2765_ = lean_usize_land(v___x_2761_, v___x_2764_);
                v___x_2766_ = lean_array_uget_borrowed(v_buckets_2751_, v___x_2765_);
                v___x_2767_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_2750_, v___x_2766_);
                return v___x_2767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg___boxed(
    mut v_m_2770_: *mut leanh::LeanObject,
    mut v_a_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v_m_2770_, v_a_2771_);
    leanh::lean_dec(v_a_2771_);
    leanh::lean_dec_ref(v_m_2770_);
    return v_res_2772_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(
    mut v_as_x27_2773_: *mut leanh::LeanObject,
    mut v_b_2774_: *mut leanh::LeanObject,
    mut v___y_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2773_) == 0 {
                    v___x_2777_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2777_, 0, v_b_2774_);
                    return v___x_2777_;
                } else {
                    v_head_2778_ = leanh::lean_ctor_get(v_as_x27_2773_, 0);
                    v_tail_2779_ = leanh::lean_ctor_get(v_as_x27_2773_, 1);
                    v___x_2780_ = lean_st_ref_take(v___y_2775_);
                    v_env_2781_ = leanh::lean_ctor_get(v___x_2780_, 0);
                    v_remaining_2782_ = leanh::lean_ctor_get(v___x_2780_, 1);
                    v_pending_2783_ = leanh::lean_ctor_get(v___x_2780_, 2);
                    v_postponedConstructors_2784_ = leanh::lean_ctor_get(v___x_2780_, 3);
                    v_postponedRecursors_2785_ = leanh::lean_ctor_get(v___x_2780_, 4);
                    v_isSharedCheck_2798_ = (!leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2798_ == 0 {
                        v___x_2787_ = v___x_2780_;
                        v_isShared_2788_ = v_isSharedCheck_2798_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_postponedRecursors_2785_);
                        leanh::lean_inc(v_postponedConstructors_2784_);
                        leanh::lean_inc(v_pending_2783_);
                        leanh::lean_inc(v_remaining_2782_);
                        leanh::lean_inc(v_env_2781_);
                        leanh::lean_dec(v___x_2780_);
                        v___x_2787_ = leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2798_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2789_ = l_Lean_ConstantInfo_name(v_head_2778_);
                v___x_2790_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v___x_2789_, v_remaining_2782_);
                v___x_2791_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v___x_2789_, v_pending_2783_);
                leanh::lean_dec(v___x_2789_);
                if v_isShared_2788_ == 0 {
                    leanh::lean_ctor_set(v___x_2787_, 2, v___x_2791_);
                    leanh::lean_ctor_set(v___x_2787_, 1, v___x_2790_);
                    v___x_2793_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_env_2781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 2, v___x_2791_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2797_,
                        3,
                        v_postponedConstructors_2784_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2797_,
                        4,
                        v_postponedRecursors_2785_,
                    );
                    v___x_2793_ = v_reuseFailAlloc_2797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2794_ = lean_st_ref_set(v___y_2775_, v___x_2793_);
                v___x_2795_ = leanh::lean_box(0);
                v_as_x27_2773_ = v_tail_2779_;
                v_b_2774_ = v___x_2795_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg___boxed(
    mut v_as_x27_2799_: *mut leanh::LeanObject,
    mut v_b_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2803_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_2799_, v_b_2800_, v___y_2801_);
    leanh::lean_dec(v___y_2801_);
    leanh::lean_dec(v_as_x27_2799_);
    return v_res_2803_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__1(
    mut v_a_2804_: *mut leanh::LeanObject,
    mut v_a_2805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2804_) == 0 {
                    v___x_2806_ = l_List_reverse___redArg(v_a_2805_);
                    return v___x_2806_;
                } else {
                    v_head_2807_ = leanh::lean_ctor_get(v_a_2804_, 0);
                    v_tail_2808_ = leanh::lean_ctor_get(v_a_2804_, 1);
                    v_isSharedCheck_2819_ = (!leanh::lean_is_exclusive(v_a_2804_)) as u8;
                    if v_isSharedCheck_2819_ == 0 {
                        v___x_2810_ = v_a_2804_;
                        v_isShared_2811_ = v_isSharedCheck_2819_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2808_);
                        leanh::lean_inc(v_head_2807_);
                        leanh::lean_dec(v_a_2804_);
                        v___x_2810_ = leanh::lean_box(0);
                        v_isShared_2811_ = v_isSharedCheck_2819_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2812_ = l_Lean_ConstantInfo_name(v_head_2807_);
                v___x_2813_ = l_Lean_ConstantInfo_type(v_head_2807_);
                leanh::lean_dec(v_head_2807_);
                v___x_2814_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2814_, 0, v___x_2812_);
                leanh::lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                if v_isShared_2811_ == 0 {
                    leanh::lean_ctor_set(v___x_2810_, 1, v_a_2805_);
                    leanh::lean_ctor_set(v___x_2810_, 0, v___x_2814_);
                    v___x_2816_ = v___x_2810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_a_2805_);
                    v___x_2816_ = v_reuseFailAlloc_2818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2804_ = v_tail_2808_;
                v_a_2805_ = v___x_2816_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__9(
    mut v_a_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v_fst_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2820_) == 0 {
                    v___x_2822_ = l_List_reverse___redArg(v_a_2821_);
                    return v___x_2822_;
                } else {
                    v_head_2823_ = leanh::lean_ctor_get(v_a_2820_, 0);
                    v_tail_2824_ = leanh::lean_ctor_get(v_a_2820_, 1);
                    v_isSharedCheck_2839_ = (!leanh::lean_is_exclusive(v_a_2820_)) as u8;
                    if v_isSharedCheck_2839_ == 0 {
                        v___x_2826_ = v_a_2820_;
                        v_isShared_2827_ = v_isSharedCheck_2839_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2824_);
                        leanh::lean_inc(v_head_2823_);
                        leanh::lean_dec(v_a_2820_);
                        v___x_2826_ = leanh::lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2839_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2828_ = leanh::lean_ctor_get(v_head_2823_, 0);
                leanh::lean_inc(v_fst_2828_);
                v_snd_2829_ = leanh::lean_ctor_get(v_head_2823_, 1);
                leanh::lean_inc(v_snd_2829_);
                leanh::lean_dec(v_head_2823_);
                v___x_2830_ = l_Lean_ConstantInfo_name(v_fst_2828_);
                v___x_2831_ = l_Lean_ConstantInfo_type(v_fst_2828_);
                leanh::lean_dec(v_fst_2828_);
                v___x_2832_ = leanh::lean_box(0);
                v___x_2833_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__1(v_snd_2829_, v___x_2832_);
                v___x_2834_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2834_, 0, v___x_2830_);
                leanh::lean_ctor_set(v___x_2834_, 1, v___x_2831_);
                leanh::lean_ctor_set(v___x_2834_, 2, v___x_2833_);
                if v_isShared_2827_ == 0 {
                    leanh::lean_ctor_set(v___x_2826_, 1, v_a_2821_);
                    leanh::lean_ctor_set(v___x_2826_, 0, v___x_2834_);
                    v___x_2836_ = v___x_2826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2838_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2821_);
                    v___x_2836_ = v_reuseFailAlloc_2838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2820_ = v_tail_2824_;
                v_a_2821_ = v___x_2836_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(
    mut v_as_x27_2845_: *mut leanh::LeanObject,
    mut v_b_2846_: *mut leanh::LeanObject,
    mut v___y_2847_: *mut leanh::LeanObject,
    mut v___y_2848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2845_) == 0 {
                    v___x_2850_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2850_, 0, v_b_2846_);
                    return v___x_2850_;
                } else {
                    v_head_2851_ = leanh::lean_ctor_get(v_as_x27_2845_, 0);
                    v_tail_2852_ = leanh::lean_ctor_get(v_as_x27_2845_, 1);
                    leanh::lean_inc(v_head_2851_);
                    v___x_2853_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_head_2851_);
                    v___x_2854_ =
                        l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
                            v___x_2853_,
                            v___y_2847_,
                            v___y_2848_,
                        );
                    if leanh::lean_obj_tag(v___x_2854_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2854_, 1);
                        v___x_2855_ = leanh::lean_box(0);
                        v_as_x27_2845_ = v_tail_2852_;
                        v_b_2846_ = v___x_2855_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2854_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(
    mut v_as_x27_2857_: *mut leanh::LeanObject,
    mut v_b_2858_: *mut leanh::LeanObject,
    mut v___y_2859_: *mut leanh::LeanObject,
    mut v___y_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2857_) == 0 {
                    v___x_2862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2862_, 0, v_b_2858_);
                    return v___x_2862_;
                } else {
                    v_head_2863_ = leanh::lean_ctor_get(v_as_x27_2857_, 0);
                    v_tail_2864_ = leanh::lean_ctor_get(v_as_x27_2857_, 1);
                    v_snd_2865_ = leanh::lean_ctor_get(v_head_2863_, 1);
                    v___x_2866_ = leanh::lean_box(0);
                    v___x_2867_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(v_snd_2865_, v___x_2866_, v___y_2859_, v___y_2860_);
                    if leanh::lean_obj_tag(v___x_2867_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2867_, 1);
                        v_as_x27_2857_ = v_tail_2864_;
                        v_b_2858_ = v___x_2866_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2867_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6;
    v___x_2873_ = leanh::lean_unsigned_to_nat(50);
    v___x_2874_ = leanh::lean_unsigned_to_nat(76);
    v___x_2875_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__5;
    v___x_2876_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__4;
    v___x_2877_ = l_mkPanicMessageWithDecl(
        v___x_2876_,
        v___x_2875_,
        v___x_2874_,
        v___x_2873_,
        v___x_2872_,
    );
    return v___x_2877_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
    mut v_name_2878_: *mut leanh::LeanObject,
    mut v_a_2879_: *mut leanh::LeanObject,
    mut v_a_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2901_: u8 = 0;
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v_a_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2925_: u8 = 0;
    let mut v_a_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_a_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_val_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_val_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2983_: u8 = 0;
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3048_: u8 = 0;
    let mut v_name_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_val_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pending_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v_name_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_unused_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_a_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_name_2878_);
                v___x_2882_ = l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(
                    v_name_2878_,
                    v_a_2880_,
                );
                if leanh::lean_obj_tag(v___x_2882_) == 0 {
                    v_a_2883_ = leanh::lean_ctor_get(v___x_2882_, 0);
                    v_isSharedCheck_3083_ = (!leanh::lean_is_exclusive(v___x_2882_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_2885_ = v___x_2882_;
                        v_isShared_2886_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2883_);
                        leanh::lean_dec(v___x_2882_);
                        v___x_2885_ = leanh::lean_box(0);
                        v_isShared_2886_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_2878_);
                    v_a_3084_ = leanh::lean_ctor_get(v___x_2882_, 0);
                    v_isSharedCheck_3091_ = (!leanh::lean_is_exclusive(v___x_2882_)) as u8;
                    if v_isSharedCheck_3091_ == 0 {
                        v___x_3086_ = v___x_2882_;
                        v_isShared_3087_ = v_isSharedCheck_3091_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3084_);
                        leanh::lean_dec(v___x_2882_);
                        v___x_3086_ = leanh::lean_box(0);
                        v_isShared_3087_ = v_isSharedCheck_3091_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2887_ = (leanh::lean_unbox(v_a_2883_) as u8);
                leanh::lean_dec(v_a_2883_);
                if v___x_2887_ == 0 {
                    leanh::lean_dec(v_name_2878_);
                    v___x_2888_ = leanh::lean_box(0);
                    if v_isShared_2886_ == 0 {
                        leanh::lean_ctor_set(v___x_2885_, 0, v___x_2888_);
                        v___x_2890_ = v___x_2885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
                        v___x_2890_ = v_reuseFailAlloc_2891_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v_a_2879_, v_name_2878_);
                    if leanh::lean_obj_tag(v___x_2892_) == 1 {
                        v_val_2893_ = leanh::lean_ctor_get(v___x_2892_, 0);
                        v_isSharedCheck_3080_ =
                            (!leanh::lean_is_exclusive(v___x_2892_)) as u8;
                        if v_isSharedCheck_3080_ == 0 {
                            v___x_2895_ = v___x_2892_;
                            v_isShared_2896_ = v_isSharedCheck_3080_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2893_);
                            leanh::lean_dec(v___x_2892_);
                            v___x_2895_ = leanh::lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_3080_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2892_);
                        leanh::lean_del_object(v___x_2885_);
                        leanh::lean_dec(v_name_2878_);
                        v___x_3081_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7_once), _init_l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7);
                        v___x_3082_ = l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10(v___x_3081_, v_a_2879_, v_a_2880_);
                        return v___x_3082_;
                    }
                }
            }
            2 => {
                return v___x_2890_;
            }
            3 => {
                leanh::lean_inc(v_val_2893_);
                v___x_2897_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_2893_);
                v___x_2898_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
                    v___x_2897_,
                    v_a_2879_,
                    v_a_2880_,
                );
                if leanh::lean_obj_tag(v___x_2898_) == 0 {
                    v_isSharedCheck_3078_ = (!leanh::lean_is_exclusive(v___x_2898_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v_unused_3079_ = leanh::lean_ctor_get(v___x_2898_, 0);
                        leanh::lean_dec(v_unused_3079_);
                        v___x_2900_ = v___x_2898_;
                        v_isShared_2901_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2898_);
                        v___x_2900_ = leanh::lean_box(0);
                        v_isShared_2901_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2895_);
                    leanh::lean_dec(v_val_2893_);
                    leanh::lean_del_object(v___x_2885_);
                    leanh::lean_dec(v_name_2878_);
                    return v___x_2898_;
                }
            }
            4 => {
                v___x_2902_ = lean_st_ref_get(v_a_2880_);
                v_pending_2903_ = leanh::lean_ctor_get(v___x_2902_, 2);
                leanh::lean_inc(v_pending_2903_);
                leanh::lean_dec(v___x_2902_);
                v___x_2904_ = l_Lean_NameSet_contains(v_pending_2903_, v_name_2878_);
                leanh::lean_dec(v_pending_2903_);
                if v___x_2904_ == 0 {
                    leanh::lean_del_object(v___x_2900_);
                    leanh::lean_del_object(v___x_2895_);
                    leanh::lean_dec(v_val_2893_);
                    leanh::lean_dec(v_name_2878_);
                    v___x_2932_ = leanh::lean_box(0);
                    if v_isShared_2886_ == 0 {
                        leanh::lean_ctor_set(v___x_2885_, 0, v___x_2932_);
                        v___x_2934_ = v___x_2885_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
                        v___x_2934_ = v_reuseFailAlloc_2935_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_name_2878_);
                    v___f_2936_ = leanh::lean_alloc_closure(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
                    leanh::lean_closure_set(v___f_2936_, 0, v_name_2878_);
                    match leanh::lean_obj_tag(v_val_2893_) {
                        0 => {
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v_val_2937_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            v_isSharedCheck_2948_ =
                                (!leanh::lean_is_exclusive(v_val_2893_)) as u8;
                            if v_isSharedCheck_2948_ == 0 {
                                v___x_2939_ = v_val_2893_;
                                v_isShared_2940_ = v_isSharedCheck_2948_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2937_);
                                leanh::lean_dec(v_val_2893_);
                                v___x_2939_ = leanh::lean_box(0);
                                v_isShared_2940_ = v_isSharedCheck_2948_;
                                state = 12;
                                continue;
                            }
                        }
                        1 => {
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v_val_2949_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            v_isSharedCheck_2960_ =
                                (!leanh::lean_is_exclusive(v_val_2893_)) as u8;
                            if v_isSharedCheck_2960_ == 0 {
                                v___x_2951_ = v_val_2893_;
                                v_isShared_2952_ = v_isSharedCheck_2960_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2949_);
                                leanh::lean_dec(v_val_2893_);
                                v___x_2951_ = leanh::lean_box(0);
                                v_isShared_2952_ = v_isSharedCheck_2960_;
                                state = 14;
                                continue;
                            }
                        }
                        2 => {
                            v_val_2961_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            leanh::lean_inc_ref_n(v_val_2961_, 2);
                            v___x_2962_ = lean_st_ref_get(v_a_2880_);
                            v_env_2963_ = leanh::lean_ctor_get(v___x_2962_, 0);
                            leanh::lean_inc_ref(v_env_2963_);
                            leanh::lean_dec(v___x_2962_);
                            leanh::lean_inc_ref(v___f_2936_);
                            v___f_2964_ = leanh::lean_alloc_closure(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1___boxed as *mut core::ffi::c_void, 6, 2);
                            leanh::lean_closure_set(v___f_2964_, 0, v_val_2961_);
                            leanh::lean_closure_set(v___f_2964_, 1, v___f_2936_);
                            v___x_2968_ = l_Lean_ConstantInfo_name(v_val_2893_);
                            leanh::lean_dec_ref_known(v_val_2893_, 1);
                            v___x_2969_ = lean_environment_find(v_env_2963_, v___x_2968_);
                            if leanh::lean_obj_tag(v___x_2969_) == 1 {
                                v_val_2970_ = leanh::lean_ctor_get(v___x_2969_, 0);
                                leanh::lean_inc(v_val_2970_);
                                if leanh::lean_obj_tag(v_val_2970_) == 2 {
                                    leanh::lean_dec_ref_known(v___x_2969_, 1);
                                    leanh::lean_dec_ref(v___f_2964_);
                                    v_toConstantVal_2971_ =
                                        leanh::lean_ctor_get(v_val_2961_, 0);
                                    v_val_2972_ = leanh::lean_ctor_get(v_val_2970_, 0);
                                    leanh::lean_inc_ref(v_val_2972_);
                                    leanh::lean_dec_ref_known(v_val_2970_, 1);
                                    v_toConstantVal_2973_ =
                                        leanh::lean_ctor_get(v_val_2972_, 0);
                                    leanh::lean_inc_ref(v_toConstantVal_2973_);
                                    v_all_2974_ = leanh::lean_ctor_get(v_val_2961_, 2);
                                    v_name_2975_ =
                                        leanh::lean_ctor_get(v_toConstantVal_2971_, 0);
                                    v_levelParams_2976_ =
                                        leanh::lean_ctor_get(v_toConstantVal_2971_, 1);
                                    v_type_2977_ =
                                        leanh::lean_ctor_get(v_toConstantVal_2971_, 2);
                                    v_all_2978_ = leanh::lean_ctor_get(v_val_2972_, 2);
                                    leanh::lean_inc(v_all_2978_);
                                    leanh::lean_dec_ref(v_val_2972_);
                                    v_name_2979_ =
                                        leanh::lean_ctor_get(v_toConstantVal_2973_, 0);
                                    leanh::lean_inc(v_name_2979_);
                                    v_levelParams_2980_ =
                                        leanh::lean_ctor_get(v_toConstantVal_2973_, 1);
                                    leanh::lean_inc(v_levelParams_2980_);
                                    v_type_2981_ =
                                        leanh::lean_ctor_get(v_toConstantVal_2973_, 2);
                                    leanh::lean_inc_ref(v_type_2981_);
                                    leanh::lean_dec_ref(v_toConstantVal_2973_);
                                    v___x_2990_ = lean_name_eq(v_name_2975_, v_name_2979_);
                                    leanh::lean_dec(v_name_2979_);
                                    if v___x_2990_ == 0 {
                                        leanh::lean_dec_ref(v_type_2981_);
                                        v___y_2983_ = v___x_2990_;
                                        state = 17;
                                        continue;
                                    } else {
                                        v___x_2991_ = lean_expr_eqv(v_type_2977_, v_type_2981_);
                                        leanh::lean_dec_ref(v_type_2981_);
                                        v___y_2983_ = v___x_2991_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_2970_);
                                    leanh::lean_dec_ref(v_val_2961_);
                                    leanh::lean_dec_ref(v___f_2936_);
                                    leanh::lean_del_object(v___x_2885_);
                                    v___x_2992_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(v___f_2964_, v___x_2969_, v_a_2879_, v_a_2880_);
                                    leanh::lean_dec_ref_known(v___x_2969_, 1);
                                    v___y_2921_ = v___x_2992_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_val_2961_);
                                leanh::lean_dec_ref(v___f_2936_);
                                leanh::lean_del_object(v___x_2885_);
                                v___x_2993_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(v___f_2964_, v___x_2969_, v_a_2879_, v_a_2880_);
                                leanh::lean_dec(v___x_2969_);
                                v___y_2921_ = v___x_2993_;
                                state = 8;
                                continue;
                            }
                        }
                        3 => {
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v_val_2994_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            v_isSharedCheck_3005_ =
                                (!leanh::lean_is_exclusive(v_val_2893_)) as u8;
                            if v_isSharedCheck_3005_ == 0 {
                                v___x_2996_ = v_val_2893_;
                                v_isShared_2997_ = v_isSharedCheck_3005_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2994_);
                                leanh::lean_dec(v_val_2893_);
                                v___x_2996_ = leanh::lean_box(0);
                                v_isShared_2997_ = v_isSharedCheck_3005_;
                                state = 19;
                                continue;
                            }
                        }
                        4 => {
                            leanh::lean_dec_ref_known(v_val_2893_, 1);
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v___x_3006_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3;
                            v___x_3007_ =
                                l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
                                    v___x_3006_,
                                    v_a_2879_,
                                    v_a_2880_,
                                );
                            if leanh::lean_obj_tag(v___x_3007_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3007_, 1);
                                v___x_3008_ = leanh::lean_box(4);
                                v___x_3009_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v___x_3008_, v_a_2880_);
                                if leanh::lean_obj_tag(v___x_3009_) == 0 {
                                    v_a_3010_ = leanh::lean_ctor_get(v___x_3009_, 0);
                                    leanh::lean_inc(v_a_3010_);
                                    leanh::lean_dec_ref_known(v___x_3009_, 1);
                                    v___x_3011_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(v_name_2878_, v_a_3010_, v_a_2879_, v_a_2880_);
                                    v___y_2921_ = v___x_3011_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_a_3012_ = leanh::lean_ctor_get(v___x_3009_, 0);
                                    leanh::lean_inc(v_a_3012_);
                                    leanh::lean_dec_ref_known(v___x_3009_, 1);
                                    v_a_2906_ = v_a_3012_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_3013_ = leanh::lean_ctor_get(v___x_3007_, 0);
                                leanh::lean_inc(v_a_3013_);
                                leanh::lean_dec_ref_known(v___x_3007_, 1);
                                v_a_2906_ = v_a_3013_;
                                state = 5;
                                continue;
                            }
                        }
                        5 => {
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v_val_3014_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            leanh::lean_inc_ref(v_val_3014_);
                            leanh::lean_dec_ref_known(v_val_2893_, 1);
                            v_toConstantVal_3015_ = leanh::lean_ctor_get(v_val_3014_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_3015_);
                            v_numParams_3016_ = leanh::lean_ctor_get(v_val_3014_, 1);
                            leanh::lean_inc(v_numParams_3016_);
                            v_all_3017_ = leanh::lean_ctor_get(v_val_3014_, 3);
                            leanh::lean_inc(v_all_3017_);
                            leanh::lean_dec_ref(v_val_3014_);
                            v___x_3018_ = leanh::lean_box(0);
                            v___x_3019_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_all_3017_, v___x_3018_, v_a_2879_);
                            if leanh::lean_obj_tag(v___x_3019_) == 0 {
                                v_a_3020_ = leanh::lean_ctor_get(v___x_3019_, 0);
                                leanh::lean_inc(v_a_3020_);
                                leanh::lean_dec_ref_known(v___x_3019_, 1);
                                v___x_3021_ = leanh::lean_box(0);
                                v___x_3022_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(v_a_3020_, v___x_3021_, v_a_2880_);
                                if leanh::lean_obj_tag(v___x_3022_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3022_, 1);
                                    v___x_3023_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7(v_a_3020_, v___x_3018_, v_a_2879_, v_a_2880_);
                                    if leanh::lean_obj_tag(v___x_3023_) == 0 {
                                        v_a_3024_ = leanh::lean_ctor_get(v___x_3023_, 0);
                                        leanh::lean_inc(v_a_3024_);
                                        leanh::lean_dec_ref_known(v___x_3023_, 1);
                                        v___x_3025_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(v_a_3024_, v___x_3021_, v_a_2879_, v_a_2880_);
                                        if leanh::lean_obj_tag(v___x_3025_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_3025_, 1);
                                            v_levelParams_3026_ = leanh::lean_ctor_get(
                                                v_toConstantVal_3015_,
                                                1,
                                            );
                                            leanh::lean_inc(v_levelParams_3026_);
                                            leanh::lean_dec_ref(v_toConstantVal_3015_);
                                            v___x_3027_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__9(v_a_3024_, v___x_3018_);
                                            v___x_3028_ = 0;
                                            v___x_3029_ =
                                                leanh::lean_alloc_ctor(6, 3, (1) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3029_,
                                                0,
                                                v_levelParams_3026_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3029_,
                                                1,
                                                v_numParams_3016_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3029_,
                                                2,
                                                v___x_3027_,
                                            );
                                            leanh::lean_ctor_set_uint8(
                                                v___x_3029_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 3)
                                                    as u32,
                                                v___x_3028_,
                                            );
                                            v___x_3030_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v___x_3029_, v_a_2880_);
                                            leanh::lean_dec_ref_known(v___x_3029_, 3);
                                            if leanh::lean_obj_tag(v___x_3030_) == 0 {
                                                v_a_3031_ =
                                                    leanh::lean_ctor_get(v___x_3030_, 0);
                                                leanh::lean_inc(v_a_3031_);
                                                leanh::lean_dec_ref_known(v___x_3030_, 1);
                                                v___x_3032_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(v_name_2878_, v_a_3031_, v_a_2879_, v_a_2880_);
                                                v___y_2921_ = v___x_3032_;
                                                state = 8;
                                                continue;
                                            } else {
                                                v_a_3033_ =
                                                    leanh::lean_ctor_get(v___x_3030_, 0);
                                                leanh::lean_inc(v_a_3033_);
                                                leanh::lean_dec_ref_known(v___x_3030_, 1);
                                                v_a_2906_ = v_a_3033_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_3024_);
                                            leanh::lean_dec(v_numParams_3016_);
                                            leanh::lean_dec_ref(v_toConstantVal_3015_);
                                            v_a_3034_ = leanh::lean_ctor_get(v___x_3025_, 0);
                                            leanh::lean_inc(v_a_3034_);
                                            leanh::lean_dec_ref_known(v___x_3025_, 1);
                                            v_a_2906_ = v_a_3034_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_numParams_3016_);
                                        leanh::lean_dec_ref(v_toConstantVal_3015_);
                                        v_a_3035_ = leanh::lean_ctor_get(v___x_3023_, 0);
                                        leanh::lean_inc(v_a_3035_);
                                        leanh::lean_dec_ref_known(v___x_3023_, 1);
                                        v_a_2906_ = v_a_3035_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3020_);
                                    leanh::lean_dec(v_numParams_3016_);
                                    leanh::lean_dec_ref(v_toConstantVal_3015_);
                                    v_a_3036_ = leanh::lean_ctor_get(v___x_3022_, 0);
                                    leanh::lean_inc(v_a_3036_);
                                    leanh::lean_dec_ref_known(v___x_3022_, 1);
                                    v_a_2906_ = v_a_3036_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_numParams_3016_);
                                leanh::lean_dec_ref(v_toConstantVal_3015_);
                                v_a_3037_ = leanh::lean_ctor_get(v___x_3019_, 0);
                                leanh::lean_inc(v_a_3037_);
                                leanh::lean_dec_ref_known(v___x_3019_, 1);
                                v_a_2906_ = v_a_3037_;
                                state = 5;
                                continue;
                            }
                        }
                        6 => {
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v_val_3038_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            leanh::lean_inc_ref(v_val_3038_);
                            leanh::lean_dec_ref_known(v_val_2893_, 1);
                            v___x_3039_ = lean_st_ref_take(v_a_2880_);
                            v_toConstantVal_3040_ = leanh::lean_ctor_get(v_val_3038_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_3040_);
                            leanh::lean_dec_ref(v_val_3038_);
                            v_env_3041_ = leanh::lean_ctor_get(v___x_3039_, 0);
                            v_remaining_3042_ = leanh::lean_ctor_get(v___x_3039_, 1);
                            v_pending_3043_ = leanh::lean_ctor_get(v___x_3039_, 2);
                            v_postponedConstructors_3044_ =
                                leanh::lean_ctor_get(v___x_3039_, 3);
                            v_postponedRecursors_3045_ =
                                leanh::lean_ctor_get(v___x_3039_, 4);
                            v_isSharedCheck_3057_ =
                                (!leanh::lean_is_exclusive(v___x_3039_)) as u8;
                            if v_isSharedCheck_3057_ == 0 {
                                v___x_3047_ = v___x_3039_;
                                v_isShared_3048_ = v_isSharedCheck_3057_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_postponedRecursors_3045_);
                                leanh::lean_inc(v_postponedConstructors_3044_);
                                leanh::lean_inc(v_pending_3043_);
                                leanh::lean_inc(v_remaining_3042_);
                                leanh::lean_inc(v_env_3041_);
                                leanh::lean_dec(v___x_3039_);
                                v___x_3047_ = leanh::lean_box(0);
                                v_isShared_3048_ = v_isSharedCheck_3057_;
                                state = 21;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2885_);
                            v_val_3058_ = leanh::lean_ctor_get(v_val_2893_, 0);
                            leanh::lean_inc_ref(v_val_3058_);
                            leanh::lean_dec_ref_known(v_val_2893_, 1);
                            v___x_3059_ = lean_st_ref_take(v_a_2880_);
                            v_toConstantVal_3060_ = leanh::lean_ctor_get(v_val_3058_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_3060_);
                            leanh::lean_dec_ref(v_val_3058_);
                            v_env_3061_ = leanh::lean_ctor_get(v___x_3059_, 0);
                            v_remaining_3062_ = leanh::lean_ctor_get(v___x_3059_, 1);
                            v_pending_3063_ = leanh::lean_ctor_get(v___x_3059_, 2);
                            v_postponedConstructors_3064_ =
                                leanh::lean_ctor_get(v___x_3059_, 3);
                            v_postponedRecursors_3065_ =
                                leanh::lean_ctor_get(v___x_3059_, 4);
                            v_isSharedCheck_3077_ =
                                (!leanh::lean_is_exclusive(v___x_3059_)) as u8;
                            if v_isSharedCheck_3077_ == 0 {
                                v___x_3067_ = v___x_3059_;
                                v_isShared_3068_ = v_isSharedCheck_3077_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_postponedRecursors_3065_);
                                leanh::lean_inc(v_postponedConstructors_3064_);
                                leanh::lean_inc(v_pending_3063_);
                                leanh::lean_inc(v_remaining_3062_);
                                leanh::lean_inc(v_env_3061_);
                                leanh::lean_dec(v___x_3059_);
                                v___x_3067_ = leanh::lean_box(0);
                                v_isShared_3068_ = v_isSharedCheck_3077_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                v___x_2907_ =
                    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__0;
                v___x_2908_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_2878_,
                    v___x_2904_,
                );
                v___x_2909_ = lean_string_append(v___x_2907_, v___x_2908_);
                leanh::lean_dec_ref(v___x_2908_);
                v___x_2910_ =
                    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1;
                v___x_2911_ = lean_string_append(v___x_2909_, v___x_2910_);
                v___x_2912_ = lean_io_error_to_string(v_a_2906_);
                v___x_2913_ = lean_string_append(v___x_2911_, v___x_2912_);
                leanh::lean_dec_ref(v___x_2912_);
                if v_isShared_2896_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2895_, 18);
                    leanh::lean_ctor_set(v___x_2895_, 0, v___x_2913_);
                    v___x_2915_ = v___x_2895_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2913_);
                    v___x_2915_ = v_reuseFailAlloc_2919_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2901_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2900_, 1);
                    leanh::lean_ctor_set(v___x_2900_, 0, v___x_2915_);
                    v___x_2917_ = v___x_2900_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2917_;
            }
            8 => {
                if leanh::lean_obj_tag(v___y_2921_) == 0 {
                    leanh::lean_del_object(v___x_2900_);
                    leanh::lean_del_object(v___x_2895_);
                    leanh::lean_dec(v_name_2878_);
                    v_a_2922_ = leanh::lean_ctor_get(v___y_2921_, 0);
                    v_isSharedCheck_2930_ = (!leanh::lean_is_exclusive(v___y_2921_)) as u8;
                    if v_isSharedCheck_2930_ == 0 {
                        v___x_2924_ = v___y_2921_;
                        v_isShared_2925_ = v_isSharedCheck_2930_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2922_);
                        leanh::lean_dec(v___y_2921_);
                        v___x_2924_ = leanh::lean_box(0);
                        v_isShared_2925_ = v_isSharedCheck_2930_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_2931_ = leanh::lean_ctor_get(v___y_2921_, 0);
                    leanh::lean_inc(v_a_2931_);
                    leanh::lean_dec_ref_known(v___y_2921_, 1);
                    v_a_2906_ = v_a_2931_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                v_a_2926_ = leanh::lean_ctor_get(v_a_2922_, 0);
                leanh::lean_inc(v_a_2926_);
                leanh::lean_dec(v_a_2922_);
                if v_isShared_2925_ == 0 {
                    leanh::lean_ctor_set(v___x_2924_, 0, v_a_2926_);
                    v___x_2928_ = v___x_2924_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2926_);
                    v___x_2928_ = v_reuseFailAlloc_2929_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2928_;
            }
            11 => {
                return v___x_2934_;
            }
            12 => {
                if v_isShared_2940_ == 0 {
                    v___x_2942_ = v___x_2939_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_val_2937_);
                    v___x_2942_ = v_reuseFailAlloc_2947_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2943_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
                    v___x_2942_,
                    v_a_2880_,
                );
                leanh::lean_dec_ref(v___x_2942_);
                if leanh::lean_obj_tag(v___x_2943_) == 0 {
                    v_a_2944_ = leanh::lean_ctor_get(v___x_2943_, 0);
                    leanh::lean_inc(v_a_2944_);
                    leanh::lean_dec_ref_known(v___x_2943_, 1);
                    v___x_2945_ =
                        l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
                            v_name_2878_,
                            v_a_2944_,
                            v_a_2879_,
                            v_a_2880_,
                        );
                    v___y_2921_ = v___x_2945_;
                    state = 8;
                    continue;
                } else {
                    v_a_2946_ = leanh::lean_ctor_get(v___x_2943_, 0);
                    leanh::lean_inc(v_a_2946_);
                    leanh::lean_dec_ref_known(v___x_2943_, 1);
                    v_a_2906_ = v_a_2946_;
                    state = 5;
                    continue;
                }
            }
            14 => {
                if v_isShared_2952_ == 0 {
                    v___x_2954_ = v___x_2951_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_val_2949_);
                    v___x_2954_ = v_reuseFailAlloc_2959_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2955_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
                    v___x_2954_,
                    v_a_2880_,
                );
                leanh::lean_dec_ref(v___x_2954_);
                if leanh::lean_obj_tag(v___x_2955_) == 0 {
                    v_a_2956_ = leanh::lean_ctor_get(v___x_2955_, 0);
                    leanh::lean_inc(v_a_2956_);
                    leanh::lean_dec_ref_known(v___x_2955_, 1);
                    v___x_2957_ =
                        l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
                            v_name_2878_,
                            v_a_2956_,
                            v_a_2879_,
                            v_a_2880_,
                        );
                    v___y_2921_ = v___x_2957_;
                    state = 8;
                    continue;
                } else {
                    v_a_2958_ = leanh::lean_ctor_get(v___x_2955_, 0);
                    leanh::lean_inc(v_a_2958_);
                    leanh::lean_dec_ref_known(v___x_2955_, 1);
                    v_a_2906_ = v_a_2958_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                v___x_2966_ = leanh::lean_box(0);
                v___x_2967_ =
                    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1(
                        v_val_2961_,
                        v___f_2936_,
                        v___x_2966_,
                        v_a_2879_,
                        v_a_2880_,
                    );
                v___y_2921_ = v___x_2967_;
                state = 8;
                continue;
            }
            17 => {
                if v___y_2983_ == 0 {
                    leanh::lean_dec(v_levelParams_2980_);
                    leanh::lean_dec(v_all_2978_);
                    leanh::lean_del_object(v___x_2885_);
                    state = 16;
                    continue;
                } else {
                    v___x_2984_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_levelParams_2976_, v_levelParams_2980_);
                    leanh::lean_dec(v_levelParams_2980_);
                    if v___x_2984_ == 0 {
                        leanh::lean_dec(v_all_2978_);
                        leanh::lean_del_object(v___x_2885_);
                        state = 16;
                        continue;
                    } else {
                        v___x_2985_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_all_2974_, v_all_2978_);
                        leanh::lean_dec(v_all_2978_);
                        if v___x_2985_ == 0 {
                            leanh::lean_del_object(v___x_2885_);
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_val_2961_);
                            leanh::lean_dec_ref(v___f_2936_);
                            leanh::lean_del_object(v___x_2900_);
                            leanh::lean_del_object(v___x_2895_);
                            leanh::lean_dec(v_name_2878_);
                            v___x_2986_ = leanh::lean_box(0);
                            if v_isShared_2886_ == 0 {
                                leanh::lean_ctor_set(v___x_2885_, 0, v___x_2986_);
                                v___x_2988_ = v___x_2885_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_2989_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2986_);
                                v___x_2988_ = v_reuseFailAlloc_2989_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            18 => {
                return v___x_2988_;
            }
            19 => {
                if v_isShared_2997_ == 0 {
                    v___x_2999_ = v___x_2996_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_val_2994_);
                    v___x_2999_ = v_reuseFailAlloc_3004_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3000_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
                    v___x_2999_,
                    v_a_2880_,
                );
                leanh::lean_dec_ref(v___x_2999_);
                if leanh::lean_obj_tag(v___x_3000_) == 0 {
                    v_a_3001_ = leanh::lean_ctor_get(v___x_3000_, 0);
                    leanh::lean_inc(v_a_3001_);
                    leanh::lean_dec_ref_known(v___x_3000_, 1);
                    v___x_3002_ =
                        l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
                            v_name_2878_,
                            v_a_3001_,
                            v_a_2879_,
                            v_a_2880_,
                        );
                    v___y_2921_ = v___x_3002_;
                    state = 8;
                    continue;
                } else {
                    v_a_3003_ = leanh::lean_ctor_get(v___x_3000_, 0);
                    leanh::lean_inc(v_a_3003_);
                    leanh::lean_dec_ref_known(v___x_3000_, 1);
                    v_a_2906_ = v_a_3003_;
                    state = 5;
                    continue;
                }
            }
            21 => {
                v_name_3049_ = leanh::lean_ctor_get(v_toConstantVal_3040_, 0);
                leanh::lean_inc(v_name_3049_);
                leanh::lean_dec_ref(v_toConstantVal_3040_);
                v___x_3050_ = l_Lean_NameSet_insert(v_postponedConstructors_3044_, v_name_3049_);
                if v_isShared_3048_ == 0 {
                    leanh::lean_ctor_set(v___x_3047_, 3, v___x_3050_);
                    v___x_3052_ = v___x_3047_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_env_3041_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_remaining_3042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_pending_3043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 3, v___x_3050_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3056_,
                        4,
                        v_postponedRecursors_3045_,
                    );
                    v___x_3052_ = v_reuseFailAlloc_3056_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_3053_ = lean_st_ref_set(v_a_2880_, v___x_3052_);
                v___x_3054_ = leanh::lean_box(0);
                v___x_3055_ =
                    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
                        v_name_2878_,
                        v___x_3054_,
                        v_a_2879_,
                        v_a_2880_,
                    );
                v___y_2921_ = v___x_3055_;
                state = 8;
                continue;
            }
            23 => {
                v_name_3069_ = leanh::lean_ctor_get(v_toConstantVal_3060_, 0);
                leanh::lean_inc(v_name_3069_);
                leanh::lean_dec_ref(v_toConstantVal_3060_);
                v___x_3070_ = l_Lean_NameSet_insert(v_postponedRecursors_3065_, v_name_3069_);
                if v_isShared_3068_ == 0 {
                    leanh::lean_ctor_set(v___x_3067_, 4, v___x_3070_);
                    v___x_3072_ = v___x_3067_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_env_3061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_remaining_3062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_pending_3063_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3076_,
                        3,
                        v_postponedConstructors_3064_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___x_3070_);
                    v___x_3072_ = v_reuseFailAlloc_3076_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3073_ = lean_st_ref_set(v_a_2880_, v___x_3072_);
                v___x_3074_ = leanh::lean_box(0);
                v___x_3075_ =
                    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
                        v_name_2878_,
                        v___x_3074_,
                        v_a_2879_,
                        v_a_2880_,
                    );
                v___y_2921_ = v___x_3075_;
                state = 8;
                continue;
            }
            25 => {
                if v_isShared_3087_ == 0 {
                    v___x_3089_ = v___x_3086_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
                    v___x_3089_ = v_reuseFailAlloc_3090_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(
    mut v_init_3092_: *mut leanh::LeanObject,
    mut v_x_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
    mut v___y_3095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3093_) == 0 {
                    v_k_3097_ = leanh::lean_ctor_get(v_x_3093_, 1);
                    leanh::lean_inc(v_k_3097_);
                    v_l_3098_ = leanh::lean_ctor_get(v_x_3093_, 3);
                    leanh::lean_inc(v_l_3098_);
                    v_r_3099_ = leanh::lean_ctor_get(v_x_3093_, 4);
                    leanh::lean_inc(v_r_3099_);
                    leanh::lean_dec_ref_known(v_x_3093_, 5);
                    v___x_3100_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v_init_3092_, v_l_3098_, v___y_3094_, v___y_3095_);
                    if leanh::lean_obj_tag(v___x_3100_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3100_, 1);
                        v___x_3101_ =
                            l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
                                v_k_3097_,
                                v___y_3094_,
                                v___y_3095_,
                            );
                        if leanh::lean_obj_tag(v___x_3101_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3101_, 1);
                            v___x_3102_ = leanh::lean_box(0);
                            v_init_3092_ = v___x_3102_;
                            v_x_3093_ = v_r_3099_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_3099_);
                            v_a_3104_ = leanh::lean_ctor_get(v___x_3101_, 0);
                            v_isSharedCheck_3111_ =
                                (!leanh::lean_is_exclusive(v___x_3101_)) as u8;
                            if v_isSharedCheck_3111_ == 0 {
                                v___x_3106_ = v___x_3101_;
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3104_);
                                leanh::lean_dec(v___x_3101_);
                                v___x_3106_ = leanh::lean_box(0);
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_r_3099_);
                        leanh::lean_dec(v_k_3097_);
                        return v___x_3100_;
                    }
                } else {
                    v___x_3112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3112_, 0, v_init_3092_);
                    v___x_3113_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3113_, 0, v___x_3112_);
                    return v___x_3113_;
                }
            }
            1 => {
                if v_isShared_3107_ == 0 {
                    v___x_3109_ = v___x_3106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
    mut v_names_3114_: *mut leanh::LeanObject,
    mut v_a_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_unused_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3118_ = leanh::lean_box(0);
                v___x_3119_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v___x_3118_, v_names_3114_, v_a_3115_, v_a_3116_);
                if leanh::lean_obj_tag(v___x_3119_) == 0 {
                    v_isSharedCheck_3126_ = (!leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3126_ == 0 {
                        v_unused_3127_ = leanh::lean_ctor_get(v___x_3119_, 0);
                        leanh::lean_dec(v_unused_3127_);
                        v___x_3121_ = v___x_3119_;
                        v_isShared_3122_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3119_);
                        v___x_3121_ = leanh::lean_box(0);
                        v_isShared_3122_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3128_ = leanh::lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3135_ = (!leanh::lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3130_ = v___x_3119_;
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3128_);
                        leanh::lean_dec(v___x_3119_);
                        v___x_3130_ = leanh::lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3122_ == 0 {
                    leanh::lean_ctor_set(v___x_3121_, 0, v___x_3118_);
                    v___x_3124_ = v___x_3121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3118_);
                    v___x_3124_ = v_reuseFailAlloc_3125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3124_;
            }
            3 => {
                if v_isShared_3131_ == 0 {
                    v___x_3133_ = v___x_3130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants___boxed(
    mut v_names_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3140_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
        v_names_3136_,
        v_a_3137_,
        v_a_3138_,
    );
    leanh::lean_dec(v_a_3138_);
    leanh::lean_dec_ref(v_a_3137_);
    return v_res_3140_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg___boxed(
    mut v_as_x27_3141_: *mut leanh::LeanObject,
    mut v_b_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_3141_, v_b_3142_, v___y_3143_, v___y_3144_);
    leanh::lean_dec(v___y_3144_);
    leanh::lean_dec_ref(v___y_3143_);
    leanh::lean_dec(v_as_x27_3141_);
    return v_res_3146_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg___boxed(
    mut v_as_x27_3147_: *mut leanh::LeanObject,
    mut v_b_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_3147_, v_b_3148_, v___y_3149_, v___y_3150_);
    leanh::lean_dec(v___y_3150_);
    leanh::lean_dec_ref(v___y_3149_);
    leanh::lean_dec(v_as_x27_3147_);
    return v_res_3152_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12___boxed(
    mut v_init_3153_: *mut leanh::LeanObject,
    mut v_x_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v_init_3153_, v_x_3154_, v___y_3155_, v___y_3156_);
    leanh::lean_dec(v___y_3156_);
    leanh::lean_dec_ref(v___y_3155_);
    return v_res_3158_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___boxed(
    mut v_name_3159_: *mut leanh::LeanObject,
    mut v_a_3160_: *mut leanh::LeanObject,
    mut v_a_3161_: *mut leanh::LeanObject,
    mut v_a_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3163_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
        v_name_3159_,
        v_a_3160_,
        v_a_3161_,
    );
    leanh::lean_dec(v_a_3161_);
    leanh::lean_dec_ref(v_a_3160_);
    return v_res_3163_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2(
    mut v_x_3164_: *mut leanh::LeanObject,
    mut v_x_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3169_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_x_3164_, v_x_3165_, v___y_3166_);
    return v___x_3169_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___boxed(
    mut v_x_3170_: *mut leanh::LeanObject,
    mut v_x_3171_: *mut leanh::LeanObject,
    mut v___y_3172_: *mut leanh::LeanObject,
    mut v___y_3173_: *mut leanh::LeanObject,
    mut v___y_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2(v_x_3170_, v_x_3171_, v___y_3172_, v___y_3173_);
    leanh::lean_dec(v___y_3173_);
    leanh::lean_dec_ref(v___y_3172_);
    return v_res_3175_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3(
    mut v_00_u03b2_3176_: *mut leanh::LeanObject,
    mut v_m_3177_: *mut leanh::LeanObject,
    mut v_a_3178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v_m_3177_, v_a_3178_);
    return v___x_3179_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___boxed(
    mut v_00_u03b2_3180_: *mut leanh::LeanObject,
    mut v_m_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3(v_00_u03b2_3180_, v_m_3181_, v_a_3182_);
    leanh::lean_dec(v_a_3182_);
    leanh::lean_dec_ref(v_m_3181_);
    return v_res_3183_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5(
    mut v_as_3184_: *mut leanh::LeanObject,
    mut v_as_x27_3185_: *mut leanh::LeanObject,
    mut v_b_3186_: *mut leanh::LeanObject,
    mut v_a_3187_: *mut leanh::LeanObject,
    mut v___y_3188_: *mut leanh::LeanObject,
    mut v___y_3189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_3185_, v_b_3186_, v___y_3188_, v___y_3189_);
    return v___x_3191_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___boxed(
    mut v_as_3192_: *mut leanh::LeanObject,
    mut v_as_x27_3193_: *mut leanh::LeanObject,
    mut v_b_3194_: *mut leanh::LeanObject,
    mut v_a_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5(v_as_3192_, v_as_x27_3193_, v_b_3194_, v_a_3195_, v___y_3196_, v___y_3197_);
    leanh::lean_dec(v___y_3197_);
    leanh::lean_dec_ref(v___y_3196_);
    leanh::lean_dec(v_as_x27_3193_);
    leanh::lean_dec(v_as_3192_);
    return v_res_3199_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6(
    mut v_as_3200_: *mut leanh::LeanObject,
    mut v_as_x27_3201_: *mut leanh::LeanObject,
    mut v_b_3202_: *mut leanh::LeanObject,
    mut v_a_3203_: *mut leanh::LeanObject,
    mut v___y_3204_: *mut leanh::LeanObject,
    mut v___y_3205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_3201_, v_b_3202_, v___y_3205_);
    return v___x_3207_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___boxed(
    mut v_as_3208_: *mut leanh::LeanObject,
    mut v_as_x27_3209_: *mut leanh::LeanObject,
    mut v_b_3210_: *mut leanh::LeanObject,
    mut v_a_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3215_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6(v_as_3208_, v_as_x27_3209_, v_b_3210_, v_a_3211_, v___y_3212_, v___y_3213_);
    leanh::lean_dec(v___y_3213_);
    leanh::lean_dec_ref(v___y_3212_);
    leanh::lean_dec(v_as_x27_3209_);
    leanh::lean_dec(v_as_3208_);
    return v_res_3215_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8(
    mut v_as_3216_: *mut leanh::LeanObject,
    mut v_as_x27_3217_: *mut leanh::LeanObject,
    mut v_b_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3223_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_3217_, v_b_3218_, v___y_3220_, v___y_3221_);
    return v___x_3223_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___boxed(
    mut v_as_3224_: *mut leanh::LeanObject,
    mut v_as_x27_3225_: *mut leanh::LeanObject,
    mut v_b_3226_: *mut leanh::LeanObject,
    mut v_a_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
    mut v___y_3230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3231_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8(v_as_3224_, v_as_x27_3225_, v_b_3226_, v_a_3227_, v___y_3228_, v___y_3229_);
    leanh::lean_dec(v___y_3229_);
    leanh::lean_dec_ref(v___y_3228_);
    leanh::lean_dec(v_as_x27_3225_);
    leanh::lean_dec(v_as_3224_);
    return v_res_3231_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4(
    mut v_00_u03b2_3232_: *mut leanh::LeanObject,
    mut v_a_3233_: *mut leanh::LeanObject,
    mut v_x_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_3233_, v_x_3234_);
    return v___x_3235_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___boxed(
    mut v_00_u03b2_3236_: *mut leanh::LeanObject,
    mut v_a_3237_: *mut leanh::LeanObject,
    mut v_x_3238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4(v_00_u03b2_3236_, v_a_3237_, v_x_3238_);
    leanh::lean_dec(v_x_3238_);
    leanh::lean_dec(v_a_3237_);
    return v_res_3239_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(
    mut v_init_3242_: *mut leanh::LeanObject,
    mut v_x_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_unused_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3243_) == 0 {
                    v_k_3247_ = leanh::lean_ctor_get(v_x_3243_, 1);
                    leanh::lean_inc(v_k_3247_);
                    v_l_3248_ = leanh::lean_ctor_get(v_x_3243_, 3);
                    leanh::lean_inc(v_l_3248_);
                    v_r_3249_ = leanh::lean_ctor_get(v_x_3243_, 4);
                    leanh::lean_inc(v_r_3249_);
                    leanh::lean_dec_ref_known(v_x_3243_, 5);
                    v___x_3257_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(v_init_3242_, v_l_3248_, v___y_3244_, v___y_3245_);
                    if leanh::lean_obj_tag(v___x_3257_) == 0 {
                        v_isSharedCheck_3280_ =
                            (!leanh::lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3280_ == 0 {
                            v_unused_3281_ = leanh::lean_ctor_get(v___x_3257_, 0);
                            leanh::lean_dec(v_unused_3281_);
                            v___x_3259_ = v___x_3257_;
                            v_isShared_3260_ = v_isSharedCheck_3280_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3257_);
                            v___x_3259_ = leanh::lean_box(0);
                            v_isShared_3260_ = v_isSharedCheck_3280_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_r_3249_);
                        leanh::lean_dec(v_k_3247_);
                        return v___x_3257_;
                    }
                } else {
                    v___x_3282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3282_, 0, v_init_3242_);
                    v___x_3283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3283_, 0, v___x_3282_);
                    return v___x_3283_;
                }
            }
            1 => {
                v___x_3251_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0;
                v___x_3252_ = 1;
                v___x_3253_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_k_3247_,
                    v___x_3252_,
                );
                v___x_3254_ = lean_string_append(v___x_3251_, v___x_3253_);
                leanh::lean_dec_ref(v___x_3253_);
                v___x_3255_ = lean_mk_io_user_error(v___x_3254_);
                v___x_3256_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3256_, 0, v___x_3255_);
                return v___x_3256_;
            }
            2 => {
                v___x_3261_ = lean_st_ref_get(v___y_3245_);
                v_env_3262_ = leanh::lean_ctor_get(v___x_3261_, 0);
                leanh::lean_inc_ref(v_env_3262_);
                leanh::lean_dec(v___x_3261_);
                leanh::lean_inc(v_k_3247_);
                v___x_3263_ = lean_environment_find(v_env_3262_, v_k_3247_);
                if leanh::lean_obj_tag(v___x_3263_) == 1 {
                    v_val_3264_ = leanh::lean_ctor_get(v___x_3263_, 0);
                    leanh::lean_inc(v_val_3264_);
                    leanh::lean_dec_ref_known(v___x_3263_, 1);
                    if leanh::lean_obj_tag(v_val_3264_) == 6 {
                        v_val_3265_ = leanh::lean_ctor_get(v_val_3264_, 0);
                        leanh::lean_inc_ref(v_val_3265_);
                        leanh::lean_dec_ref_known(v_val_3264_, 1);
                        v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v___y_3244_, v_k_3247_);
                        if leanh::lean_obj_tag(v___x_3266_) == 1 {
                            v_val_3267_ = leanh::lean_ctor_get(v___x_3266_, 0);
                            leanh::lean_inc(v_val_3267_);
                            leanh::lean_dec_ref_known(v___x_3266_, 1);
                            if leanh::lean_obj_tag(v_val_3267_) == 6 {
                                v_val_3268_ = leanh::lean_ctor_get(v_val_3267_, 0);
                                leanh::lean_inc_ref(v_val_3268_);
                                leanh::lean_dec_ref_known(v_val_3267_, 1);
                                v___x_3269_ =
                                    l_Lean_instBEqConstructorVal_beq(v_val_3265_, v_val_3268_);
                                leanh::lean_dec_ref(v_val_3268_);
                                leanh::lean_dec_ref(v_val_3265_);
                                if v___x_3269_ == 0 {
                                    leanh::lean_dec(v_r_3249_);
                                    v___x_3270_ = 1;
                                    v___x_3271_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1;
                                    v___x_3272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_3247_, v___x_3270_);
                                    v___x_3273_ = lean_string_append(v___x_3271_, v___x_3272_);
                                    leanh::lean_dec_ref(v___x_3272_);
                                    v___x_3274_ = lean_mk_io_user_error(v___x_3273_);
                                    if v_isShared_3260_ == 0 {
                                        leanh::lean_ctor_set_tag(v___x_3259_, 1);
                                        leanh::lean_ctor_set(v___x_3259_, 0, v___x_3274_);
                                        v___x_3276_ = v___x_3259_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3277_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3277_,
                                            0,
                                            v___x_3274_,
                                        );
                                        v___x_3276_ = v_reuseFailAlloc_3277_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3259_);
                                    leanh::lean_dec(v_k_3247_);
                                    v___x_3278_ = leanh::lean_box(0);
                                    v_init_3242_ = v___x_3278_;
                                    v_x_3243_ = v_r_3249_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_3267_);
                                leanh::lean_dec_ref(v_val_3265_);
                                leanh::lean_del_object(v___x_3259_);
                                leanh::lean_dec(v_r_3249_);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3266_);
                            leanh::lean_dec_ref(v_val_3265_);
                            leanh::lean_del_object(v___x_3259_);
                            leanh::lean_dec(v_r_3249_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3264_);
                        leanh::lean_del_object(v___x_3259_);
                        leanh::lean_dec(v_r_3249_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3263_);
                    leanh::lean_del_object(v___x_3259_);
                    leanh::lean_dec(v_r_3249_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_3276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___boxed(
    mut v_init_3284_: *mut leanh::LeanObject,
    mut v_x_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
    mut v___y_3287_: *mut leanh::LeanObject,
    mut v___y_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(v_init_3284_, v_x_3285_, v___y_3286_, v___y_3287_);
    leanh::lean_dec(v___y_3287_);
    leanh::lean_dec_ref(v___y_3286_);
    return v_res_3289_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors(
    mut v_a_3290_: *mut leanh::LeanObject,
    mut v_a_3291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_unused_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3293_ = lean_st_ref_get(v_a_3291_);
                v_postponedConstructors_3294_ = leanh::lean_ctor_get(v___x_3293_, 3);
                leanh::lean_inc(v_postponedConstructors_3294_);
                leanh::lean_dec(v___x_3293_);
                v___x_3295_ = leanh::lean_box(0);
                v___x_3296_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(v___x_3295_, v_postponedConstructors_3294_, v_a_3290_, v_a_3291_);
                if leanh::lean_obj_tag(v___x_3296_) == 0 {
                    v_isSharedCheck_3303_ = (!leanh::lean_is_exclusive(v___x_3296_)) as u8;
                    if v_isSharedCheck_3303_ == 0 {
                        v_unused_3304_ = leanh::lean_ctor_get(v___x_3296_, 0);
                        leanh::lean_dec(v_unused_3304_);
                        v___x_3298_ = v___x_3296_;
                        v_isShared_3299_ = v_isSharedCheck_3303_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3296_);
                        v___x_3298_ = leanh::lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3303_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3305_ = leanh::lean_ctor_get(v___x_3296_, 0);
                    v_isSharedCheck_3312_ = (!leanh::lean_is_exclusive(v___x_3296_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v___x_3307_ = v___x_3296_;
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3305_);
                        leanh::lean_dec(v___x_3296_);
                        v___x_3307_ = leanh::lean_box(0);
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3299_ == 0 {
                    leanh::lean_ctor_set(v___x_3298_, 0, v___x_3295_);
                    v___x_3301_ = v___x_3298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3295_);
                    v___x_3301_ = v_reuseFailAlloc_3302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3301_;
            }
            3 => {
                if v_isShared_3308_ == 0 {
                    v___x_3310_ = v___x_3307_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
                    v___x_3310_ = v_reuseFailAlloc_3311_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors___boxed(
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_a_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3316_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors(
        v_a_3313_, v_a_3314_,
    );
    leanh::lean_dec(v_a_3314_);
    leanh::lean_dec_ref(v_a_3313_);
    return v_res_3316_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(
    mut v_init_3319_: *mut leanh::LeanObject,
    mut v_x_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut v_unused_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3320_) == 0 {
                    v_k_3324_ = leanh::lean_ctor_get(v_x_3320_, 1);
                    leanh::lean_inc(v_k_3324_);
                    v_l_3325_ = leanh::lean_ctor_get(v_x_3320_, 3);
                    leanh::lean_inc(v_l_3325_);
                    v_r_3326_ = leanh::lean_ctor_get(v_x_3320_, 4);
                    leanh::lean_inc(v_r_3326_);
                    leanh::lean_dec_ref_known(v_x_3320_, 5);
                    v___x_3334_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(v_init_3319_, v_l_3325_, v___y_3321_, v___y_3322_);
                    if leanh::lean_obj_tag(v___x_3334_) == 0 {
                        v_isSharedCheck_3357_ =
                            (!leanh::lean_is_exclusive(v___x_3334_)) as u8;
                        if v_isSharedCheck_3357_ == 0 {
                            v_unused_3358_ = leanh::lean_ctor_get(v___x_3334_, 0);
                            leanh::lean_dec(v_unused_3358_);
                            v___x_3336_ = v___x_3334_;
                            v_isShared_3337_ = v_isSharedCheck_3357_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3334_);
                            v___x_3336_ = leanh::lean_box(0);
                            v_isShared_3337_ = v_isSharedCheck_3357_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_r_3326_);
                        leanh::lean_dec(v_k_3324_);
                        return v___x_3334_;
                    }
                } else {
                    v___x_3359_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3359_, 0, v_init_3319_);
                    v___x_3360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3360_, 0, v___x_3359_);
                    return v___x_3360_;
                }
            }
            1 => {
                v___x_3328_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0;
                v___x_3329_ = 1;
                v___x_3330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_k_3324_,
                    v___x_3329_,
                );
                v___x_3331_ = lean_string_append(v___x_3328_, v___x_3330_);
                leanh::lean_dec_ref(v___x_3330_);
                v___x_3332_ = lean_mk_io_user_error(v___x_3331_);
                v___x_3333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3333_, 0, v___x_3332_);
                return v___x_3333_;
            }
            2 => {
                v___x_3338_ = lean_st_ref_get(v___y_3322_);
                v_env_3339_ = leanh::lean_ctor_get(v___x_3338_, 0);
                leanh::lean_inc_ref(v_env_3339_);
                leanh::lean_dec(v___x_3338_);
                leanh::lean_inc(v_k_3324_);
                v___x_3340_ = lean_environment_find(v_env_3339_, v_k_3324_);
                if leanh::lean_obj_tag(v___x_3340_) == 1 {
                    v_val_3341_ = leanh::lean_ctor_get(v___x_3340_, 0);
                    leanh::lean_inc(v_val_3341_);
                    leanh::lean_dec_ref_known(v___x_3340_, 1);
                    if leanh::lean_obj_tag(v_val_3341_) == 7 {
                        v_val_3342_ = leanh::lean_ctor_get(v_val_3341_, 0);
                        leanh::lean_inc_ref(v_val_3342_);
                        leanh::lean_dec_ref_known(v_val_3341_, 1);
                        v___x_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v___y_3321_, v_k_3324_);
                        if leanh::lean_obj_tag(v___x_3343_) == 1 {
                            v_val_3344_ = leanh::lean_ctor_get(v___x_3343_, 0);
                            leanh::lean_inc(v_val_3344_);
                            leanh::lean_dec_ref_known(v___x_3343_, 1);
                            if leanh::lean_obj_tag(v_val_3344_) == 7 {
                                v_val_3345_ = leanh::lean_ctor_get(v_val_3344_, 0);
                                leanh::lean_inc_ref(v_val_3345_);
                                leanh::lean_dec_ref_known(v_val_3344_, 1);
                                v___x_3346_ =
                                    l_Lean_instBEqRecursorVal_beq(v_val_3342_, v_val_3345_);
                                leanh::lean_dec_ref(v_val_3345_);
                                leanh::lean_dec_ref(v_val_3342_);
                                if v___x_3346_ == 0 {
                                    leanh::lean_dec(v_r_3326_);
                                    v___x_3347_ = 1;
                                    v___x_3348_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1;
                                    v___x_3349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_3324_, v___x_3347_);
                                    v___x_3350_ = lean_string_append(v___x_3348_, v___x_3349_);
                                    leanh::lean_dec_ref(v___x_3349_);
                                    v___x_3351_ = lean_mk_io_user_error(v___x_3350_);
                                    if v_isShared_3337_ == 0 {
                                        leanh::lean_ctor_set_tag(v___x_3336_, 1);
                                        leanh::lean_ctor_set(v___x_3336_, 0, v___x_3351_);
                                        v___x_3353_ = v___x_3336_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3354_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3354_,
                                            0,
                                            v___x_3351_,
                                        );
                                        v___x_3353_ = v_reuseFailAlloc_3354_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3336_);
                                    leanh::lean_dec(v_k_3324_);
                                    v___x_3355_ = leanh::lean_box(0);
                                    v_init_3319_ = v___x_3355_;
                                    v_x_3320_ = v_r_3326_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_3344_);
                                leanh::lean_dec_ref(v_val_3342_);
                                leanh::lean_del_object(v___x_3336_);
                                leanh::lean_dec(v_r_3326_);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3343_);
                            leanh::lean_dec_ref(v_val_3342_);
                            leanh::lean_del_object(v___x_3336_);
                            leanh::lean_dec(v_r_3326_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3341_);
                        leanh::lean_del_object(v___x_3336_);
                        leanh::lean_dec(v_r_3326_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3340_);
                    leanh::lean_del_object(v___x_3336_);
                    leanh::lean_dec(v_r_3326_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_3353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___boxed(
    mut v_init_3361_: *mut leanh::LeanObject,
    mut v_x_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3366_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(v_init_3361_, v_x_3362_, v___y_3363_, v___y_3364_);
    leanh::lean_dec(v___y_3364_);
    leanh::lean_dec_ref(v___y_3363_);
    return v_res_3366_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors(
    mut v_a_3367_: *mut leanh::LeanObject,
    mut v_a_3368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut v_unused_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3370_ = lean_st_ref_get(v_a_3368_);
                v_postponedRecursors_3371_ = leanh::lean_ctor_get(v___x_3370_, 4);
                leanh::lean_inc(v_postponedRecursors_3371_);
                leanh::lean_dec(v___x_3370_);
                v___x_3372_ = leanh::lean_box(0);
                v___x_3373_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(v___x_3372_, v_postponedRecursors_3371_, v_a_3367_, v_a_3368_);
                if leanh::lean_obj_tag(v___x_3373_) == 0 {
                    v_isSharedCheck_3380_ = (!leanh::lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3380_ == 0 {
                        v_unused_3381_ = leanh::lean_ctor_get(v___x_3373_, 0);
                        leanh::lean_dec(v_unused_3381_);
                        v___x_3375_ = v___x_3373_;
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3373_);
                        v___x_3375_ = leanh::lean_box(0);
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3382_ = leanh::lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3389_ = (!leanh::lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3389_ == 0 {
                        v___x_3384_ = v___x_3373_;
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3382_);
                        leanh::lean_dec(v___x_3373_);
                        v___x_3384_ = leanh::lean_box(0);
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3376_ == 0 {
                    leanh::lean_ctor_set(v___x_3375_, 0, v___x_3372_);
                    v___x_3378_ = v___x_3375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3379_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3372_);
                    v___x_3378_ = v_reuseFailAlloc_3379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3378_;
            }
            3 => {
                if v_isShared_3385_ == 0 {
                    v___x_3387_ = v___x_3384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors___boxed(
    mut v_a_3390_: *mut leanh::LeanObject,
    mut v_a_3391_: *mut leanh::LeanObject,
    mut v_a_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors(
        v_a_3390_, v_a_3391_,
    );
    leanh::lean_dec(v_a_3391_);
    leanh::lean_dec_ref(v_a_3390_);
    return v_res_3393_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
    mut v_as_x27_3394_: *mut leanh::LeanObject,
    mut v_b_3395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3394_) == 0 {
                    v___x_3397_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3397_, 0, v_b_3395_);
                    return v___x_3397_;
                } else {
                    v_head_3398_ = leanh::lean_ctor_get(v_as_x27_3394_, 0);
                    v_tail_3399_ = leanh::lean_ctor_get(v_as_x27_3394_, 1);
                    v_fst_3400_ = leanh::lean_ctor_get(v_head_3398_, 0);
                    v_snd_3401_ = leanh::lean_ctor_get(v_head_3398_, 1);
                    v___x_3402_ = l_Lean_ConstantInfo_isUnsafe(v_snd_3401_);
                    if v___x_3402_ == 0 {
                        v___x_3403_ = l_Lean_ConstantInfo_isPartial(v_snd_3401_);
                        if v___x_3403_ == 0 {
                            leanh::lean_inc(v_fst_3400_);
                            v___x_3404_ = l_Lean_NameSet_insert(v_b_3395_, v_fst_3400_);
                            v_as_x27_3394_ = v_tail_3399_;
                            v_b_3395_ = v___x_3404_;
                            state = 0;
                            continue;
                        } else {
                            v_as_x27_3394_ = v_tail_3399_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_3394_ = v_tail_3399_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg___boxed(
    mut v_as_x27_3408_: *mut leanh::LeanObject,
    mut v_b_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
        v_as_x27_3408_,
        v_b_3409_,
    );
    leanh::lean_dec(v_as_x27_3408_);
    return v_res_3411_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(
    mut v_x_3412_: *mut leanh::LeanObject,
    mut v_x_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3413_) == 0 {
        leanh::lean_inc(v_x_3412_);
        return v_x_3412_;
    } else {
        let mut v_key_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_3414_ = leanh::lean_ctor_get(v_x_3413_, 0);
        v_value_3415_ = leanh::lean_ctor_get(v_x_3413_, 1);
        v_tail_3416_ = leanh::lean_ctor_get(v_x_3413_, 2);
        v___x_3417_ =
            l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(
                v_x_3412_,
                v_tail_3416_,
            );
        leanh::lean_inc(v_value_3415_);
        leanh::lean_inc(v_key_3414_);
        v___x_3418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3418_, 0, v_key_3414_);
        leanh::lean_ctor_set(v___x_3418_, 1, v_value_3415_);
        v___x_3419_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3419_, 0, v___x_3418_);
        leanh::lean_ctor_set(v___x_3419_, 1, v___x_3417_);
        return v___x_3419_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1___boxed(
    mut v_x_3420_: *mut leanh::LeanObject,
    mut v_x_3421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(
        v_x_3420_, v_x_3421_,
    );
    leanh::lean_dec(v_x_3421_);
    leanh::lean_dec(v_x_3420_);
    return v_res_3422_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_spec__2(
    mut v_as_3423_: *mut leanh::LeanObject,
    mut v_i_3424_: usize,
    mut v_stop_3425_: usize,
    mut v_b_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: usize = 0;
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3427_ = lean_usize_dec_eq(v_i_3424_, v_stop_3425_);
                if v___x_3427_ == 0 {
                    v___x_3428_ = 1usize;
                    v___x_3429_ = lean_usize_sub(v_i_3424_, v___x_3428_);
                    v___x_3430_ = lean_array_uget_borrowed(v_as_3423_, v___x_3429_);
                    v___x_3431_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(v_b_3426_, v___x_3430_);
                    leanh::lean_dec(v_b_3426_);
                    v_i_3424_ = v___x_3429_;
                    v_b_3426_ = v___x_3431_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3426_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_spec__2___boxed(
    mut v_as_3433_: *mut leanh::LeanObject,
    mut v_i_3434_: *mut leanh::LeanObject,
    mut v_stop_3435_: *mut leanh::LeanObject,
    mut v_b_3436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3437_: usize = 0;
    let mut v_stop_boxed_3438_: usize = 0;
    let mut v_res_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3437_ = leanh::lean_unbox_usize(v_i_3434_);
    leanh::lean_dec(v_i_3434_);
    v_stop_boxed_3438_ = leanh::lean_unbox_usize(v_stop_3435_);
    leanh::lean_dec(v_stop_3435_);
    v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_spec__2(v_as_3433_, v_i_boxed_3437_, v_stop_boxed_3438_, v_b_3436_);
    leanh::lean_dec_ref(v_as_3433_);
    return v_res_3439_;
}
pub unsafe fn l_Lean_Environment_replay(
    mut v_newConstants_3440_: *mut leanh::LeanObject,
    mut v_env_3441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_unused_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_buckets_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3465_ = leanh::lean_ctor_get(v_newConstants_3440_, 1);
                v_remaining_3466_ = l_Lean_NameSet_empty;
                v___x_3486_ = leanh::lean_box(0);
                v___x_3487_ = lean_array_get_size(v_buckets_3465_);
                v___x_3488_ = leanh::lean_unsigned_to_nat(0);
                v___x_3489_ = lean_nat_dec_lt(v___x_3488_, v___x_3487_);
                if v___x_3489_ == 0 {
                    v___y_3468_ = v___x_3486_;
                    state = 6;
                    continue;
                } else {
                    v___x_3490_ = lean_usize_of_nat(v___x_3487_);
                    v___x_3491_ = 0usize;
                    v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_spec__2(v_buckets_3465_, v___x_3490_, v___x_3491_, v___x_3486_);
                    v___y_3468_ = v___x_3492_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3445_) == 0 {
                    v_isSharedCheck_3455_ = (!leanh::lean_is_exclusive(v___y_3445_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v_unused_3456_ = leanh::lean_ctor_get(v___y_3445_, 0);
                        leanh::lean_dec(v_unused_3456_);
                        v___x_3447_ = v___y_3445_;
                        v_isShared_3448_ = v_isSharedCheck_3455_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_3445_);
                        v___x_3447_ = leanh::lean_box(0);
                        v_isShared_3448_ = v_isSharedCheck_3455_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_3444_);
                    v_a_3457_ = leanh::lean_ctor_get(v___y_3445_, 0);
                    v_isSharedCheck_3464_ = (!leanh::lean_is_exclusive(v___y_3445_)) as u8;
                    if v_isSharedCheck_3464_ == 0 {
                        v___x_3459_ = v___y_3445_;
                        v_isShared_3460_ = v_isSharedCheck_3464_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3457_);
                        leanh::lean_dec(v___y_3445_);
                        v___x_3459_ = leanh::lean_box(0);
                        v_isShared_3460_ = v_isSharedCheck_3464_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3449_ = lean_st_ref_get(v___y_3444_);
                leanh::lean_dec(v___y_3444_);
                v_env_3450_ = leanh::lean_ctor_get(v___x_3449_, 0);
                leanh::lean_inc_ref(v_env_3450_);
                leanh::lean_dec(v___x_3449_);
                v___x_3451_ = lean_elab_environment_of_kernel_env(v_env_3450_);
                if v_isShared_3448_ == 0 {
                    leanh::lean_ctor_set(v___x_3447_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3453_;
            }
            4 => {
                if v_isShared_3460_ == 0 {
                    v___x_3462_ = v___x_3459_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
                    v___x_3462_ = v_reuseFailAlloc_3463_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3462_;
            }
            6 => {
                v___x_3469_ =
                    l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
                        v___y_3468_,
                        v_remaining_3466_,
                    );
                leanh::lean_dec(v___y_3468_);
                v_a_3470_ = leanh::lean_ctor_get(v___x_3469_, 0);
                leanh::lean_inc_n(v_a_3470_, 2);
                leanh::lean_dec_ref(v___x_3469_);
                v___x_3471_ = lean_elab_environment_to_kernel_env(v_env_3441_);
                v___x_3472_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3472_, 0, v___x_3471_);
                leanh::lean_ctor_set(v___x_3472_, 1, v_a_3470_);
                leanh::lean_ctor_set(v___x_3472_, 2, v_remaining_3466_);
                leanh::lean_ctor_set(v___x_3472_, 3, v_remaining_3466_);
                leanh::lean_ctor_set(v___x_3472_, 4, v_remaining_3466_);
                v___x_3473_ = lean_st_mk_ref(v___x_3472_);
                v___x_3474_ = leanh::lean_box(0);
                v___x_3475_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v___x_3474_, v_a_3470_, v_newConstants_3440_, v___x_3473_);
                if leanh::lean_obj_tag(v___x_3475_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3475_, 1);
                    v___x_3476_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors(v_newConstants_3440_, v___x_3473_);
                    if leanh::lean_obj_tag(v___x_3476_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3476_, 1);
                        v___x_3477_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors(v_newConstants_3440_, v___x_3473_);
                        v___y_3444_ = v___x_3473_;
                        v___y_3445_ = v___x_3477_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3444_ = v___x_3473_;
                        v___y_3445_ = v___x_3476_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3473_);
                    v_a_3478_ = leanh::lean_ctor_get(v___x_3475_, 0);
                    v_isSharedCheck_3485_ = (!leanh::lean_is_exclusive(v___x_3475_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v___x_3480_ = v___x_3475_;
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3478_);
                        leanh::lean_dec(v___x_3475_);
                        v___x_3480_ = leanh::lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_3481_ == 0 {
                    v___x_3483_ = v___x_3480_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Environment_replay___boxed(
    mut v_newConstants_3493_: *mut leanh::LeanObject,
    mut v_env_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3496_ = l_Lean_Environment_replay(v_newConstants_3493_, v_env_3494_);
    leanh::lean_dec_ref(v_newConstants_3493_);
    return v_res_3496_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0(
    mut v_as_3497_: *mut leanh::LeanObject,
    mut v_as_x27_3498_: *mut leanh::LeanObject,
    mut v_b_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
        v_as_x27_3498_,
        v_b_3499_,
    );
    return v___x_3502_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___boxed(
    mut v_as_3503_: *mut leanh::LeanObject,
    mut v_as_x27_3504_: *mut leanh::LeanObject,
    mut v_b_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
    mut v___y_3507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3508_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0(
        v_as_3503_,
        v_as_x27_3504_,
        v_b_3505_,
        v_a_3506_,
    );
    leanh::lean_dec(v_as_x27_3504_);
    leanh::lean_dec(v_as_3503_);
    return v_res_3508_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Replay(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FoldConsts(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Replay(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Replay(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_FoldConsts(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Replay(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Replay(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Replay(builtin);
}