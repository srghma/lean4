// Lean compiler output
// Module: Lean.Replay
// Imports: Lean.CoreM Lean.AddDecl Lean.Util.FoldConsts
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_lt, lean_nat_mul,
    lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Environment::lean_add_decl;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0: u64 = 0;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__0_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__2_value
        ) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6_value:
    LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__5_value:
    LeanStringObject<62> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__4_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [78, 111, 32, 115, 117, 99, 104, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [78, 111, 32, 115, 117, 99, 104, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(
    mut v_k_1755_: *mut LeanObject,
    mut v_t_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v_impl_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v_size_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v_unused_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_unused_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v_size_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_unused_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v_k_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v_size_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_unused_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_unused_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v_k_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_unused_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_unused_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v_size_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2134_: u8 = 0;
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_unused_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_unused_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v_k_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut v_unused_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v_k_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_unused_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut v_unused_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_unused_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v_size_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2306_: u8 = 0;
    let mut v_unused_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2320_: u8 = 0;
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut v_unused_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v_size_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_unused_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_unused_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v_k_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v_unused_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_unused_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_unused_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1756_) == 0 {
                    v_k_1757_ = lean_ctor_get(v_t_1756_, 1);
                    v_v_1758_ = lean_ctor_get(v_t_1756_, 2);
                    v_l_1759_ = lean_ctor_get(v_t_1756_, 3);
                    v_r_1760_ = lean_ctor_get(v_t_1756_, 4);
                    v_isSharedCheck_2414_ = (!lean_is_exclusive(v_t_1756_)) as u8;
                    if v_isSharedCheck_2414_ == 0 {
                        v_unused_2415_ = lean_ctor_get(v_t_1756_, 0);
                        lean_dec(v_unused_2415_);
                        v___x_1762_ = v_t_1756_;
                        v_isShared_1763_ = v_isSharedCheck_2414_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1760_);
                        lean_inc(v_l_1759_);
                        lean_inc(v_v_1758_);
                        lean_inc(v_k_1757_);
                        lean_dec(v_t_1756_);
                        v___x_1762_ = lean_box(0);
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
                        v___x_1766_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_1765_) == 0 {
                            if lean_obj_tag(v_r_1760_) == 0 {
                                v_size_1767_ = lean_ctor_get(v_impl_1765_, 0);
                                lean_inc(v_size_1767_);
                                v_size_1768_ = lean_ctor_get(v_r_1760_, 0);
                                v_k_1769_ = lean_ctor_get(v_r_1760_, 1);
                                v_v_1770_ = lean_ctor_get(v_r_1760_, 2);
                                v_l_1771_ = lean_ctor_get(v_r_1760_, 3);
                                lean_inc(v_l_1771_);
                                v_r_1772_ = lean_ctor_get(v_r_1760_, 4);
                                v___x_1773_ = lean_unsigned_to_nat(3);
                                v___x_1774_ = lean_nat_mul(v___x_1773_, v_size_1767_);
                                v___x_1775_ = lean_nat_dec_lt(v___x_1774_, v_size_1768_);
                                lean_dec(v___x_1774_);
                                if v___x_1775_ == 0 {
                                    lean_dec(v_l_1771_);
                                    v___x_1776_ = lean_nat_add(v___x_1766_, v_size_1767_);
                                    lean_dec(v_size_1767_);
                                    v___x_1777_ = lean_nat_add(v___x_1776_, v_size_1768_);
                                    lean_dec(v___x_1776_);
                                    if v_isShared_1763_ == 0 {
                                        lean_ctor_set(v___x_1762_, 3, v_impl_1765_);
                                        lean_ctor_set(v___x_1762_, 0, v___x_1777_);
                                        v___x_1779_ = v___x_1762_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
                                        lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_k_1757_);
                                        lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_v_1758_);
                                        lean_ctor_set(v_reuseFailAlloc_1780_, 3, v_impl_1765_);
                                        lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_r_1760_);
                                        v___x_1779_ = v_reuseFailAlloc_1780_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_1772_);
                                    lean_inc(v_v_1770_);
                                    lean_inc(v_k_1769_);
                                    lean_inc(v_size_1768_);
                                    v_isSharedCheck_1844_ = (!lean_is_exclusive(v_r_1760_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v_unused_1845_ = lean_ctor_get(v_r_1760_, 4);
                                        lean_dec(v_unused_1845_);
                                        v_unused_1846_ = lean_ctor_get(v_r_1760_, 3);
                                        lean_dec(v_unused_1846_);
                                        v_unused_1847_ = lean_ctor_get(v_r_1760_, 2);
                                        lean_dec(v_unused_1847_);
                                        v_unused_1848_ = lean_ctor_get(v_r_1760_, 1);
                                        lean_dec(v_unused_1848_);
                                        v_unused_1849_ = lean_ctor_get(v_r_1760_, 0);
                                        lean_dec(v_unused_1849_);
                                        v___x_1782_ = v_r_1760_;
                                        v_isShared_1783_ = v_isSharedCheck_1844_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_r_1760_);
                                        v___x_1782_ = lean_box(0);
                                        v_isShared_1783_ = v_isSharedCheck_1844_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1850_ = lean_ctor_get(v_impl_1765_, 0);
                                lean_inc(v_size_1850_);
                                v___x_1851_ = lean_nat_add(v___x_1766_, v_size_1850_);
                                lean_dec(v_size_1850_);
                                if v_isShared_1763_ == 0 {
                                    lean_ctor_set(v___x_1762_, 3, v_impl_1765_);
                                    lean_ctor_set(v___x_1762_, 0, v___x_1851_);
                                    v___x_1853_ = v___x_1762_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
                                    lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_k_1757_);
                                    lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_v_1758_);
                                    lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_impl_1765_);
                                    lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_r_1760_);
                                    v___x_1853_ = v_reuseFailAlloc_1854_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_r_1760_) == 0 {
                                v_l_1855_ = lean_ctor_get(v_r_1760_, 3);
                                lean_inc(v_l_1855_);
                                if lean_obj_tag(v_l_1855_) == 0 {
                                    v_r_1856_ = lean_ctor_get(v_r_1760_, 4);
                                    lean_inc(v_r_1856_);
                                    if lean_obj_tag(v_r_1856_) == 0 {
                                        v_size_1857_ = lean_ctor_get(v_r_1760_, 0);
                                        v_k_1858_ = lean_ctor_get(v_r_1760_, 1);
                                        v_v_1859_ = lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1872_ =
                                            (!lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1872_ == 0 {
                                            v_unused_1873_ = lean_ctor_get(v_r_1760_, 4);
                                            lean_dec(v_unused_1873_);
                                            v_unused_1874_ = lean_ctor_get(v_r_1760_, 3);
                                            lean_dec(v_unused_1874_);
                                            v___x_1861_ = v_r_1760_;
                                            v_isShared_1862_ = v_isSharedCheck_1872_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1859_);
                                            lean_inc(v_k_1858_);
                                            lean_inc(v_size_1857_);
                                            lean_dec(v_r_1760_);
                                            v___x_1861_ = lean_box(0);
                                            v_isShared_1862_ = v_isSharedCheck_1872_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1875_ = lean_ctor_get(v_r_1760_, 1);
                                        v_v_1876_ = lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1899_ =
                                            (!lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1899_ == 0 {
                                            v_unused_1900_ = lean_ctor_get(v_r_1760_, 4);
                                            lean_dec(v_unused_1900_);
                                            v_unused_1901_ = lean_ctor_get(v_r_1760_, 3);
                                            lean_dec(v_unused_1901_);
                                            v_unused_1902_ = lean_ctor_get(v_r_1760_, 0);
                                            lean_dec(v_unused_1902_);
                                            v___x_1878_ = v_r_1760_;
                                            v_isShared_1879_ = v_isSharedCheck_1899_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1876_);
                                            lean_inc(v_k_1875_);
                                            lean_dec(v_r_1760_);
                                            v___x_1878_ = lean_box(0);
                                            v_isShared_1879_ = v_isSharedCheck_1899_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1903_ = lean_ctor_get(v_r_1760_, 4);
                                    lean_inc(v_r_1903_);
                                    if lean_obj_tag(v_r_1903_) == 0 {
                                        v_k_1904_ = lean_ctor_get(v_r_1760_, 1);
                                        v_v_1905_ = lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1916_ =
                                            (!lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1916_ == 0 {
                                            v_unused_1917_ = lean_ctor_get(v_r_1760_, 4);
                                            lean_dec(v_unused_1917_);
                                            v_unused_1918_ = lean_ctor_get(v_r_1760_, 3);
                                            lean_dec(v_unused_1918_);
                                            v_unused_1919_ = lean_ctor_get(v_r_1760_, 0);
                                            lean_dec(v_unused_1919_);
                                            v___x_1907_ = v_r_1760_;
                                            v_isShared_1908_ = v_isSharedCheck_1916_;
                                            state = 22;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1905_);
                                            lean_inc(v_k_1904_);
                                            lean_dec(v_r_1760_);
                                            v___x_1907_ = lean_box(0);
                                            v_isShared_1908_ = v_isSharedCheck_1916_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_1920_ = lean_ctor_get(v_r_1760_, 0);
                                        v_k_1921_ = lean_ctor_get(v_r_1760_, 1);
                                        v_v_1922_ = lean_ctor_get(v_r_1760_, 2);
                                        v_isSharedCheck_1933_ =
                                            (!lean_is_exclusive(v_r_1760_)) as u8;
                                        if v_isSharedCheck_1933_ == 0 {
                                            v_unused_1934_ = lean_ctor_get(v_r_1760_, 4);
                                            lean_dec(v_unused_1934_);
                                            v_unused_1935_ = lean_ctor_get(v_r_1760_, 3);
                                            lean_dec(v_unused_1935_);
                                            v___x_1924_ = v_r_1760_;
                                            v_isShared_1925_ = v_isSharedCheck_1933_;
                                            state = 25;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1922_);
                                            lean_inc(v_k_1921_);
                                            lean_inc(v_size_1920_);
                                            lean_dec(v_r_1760_);
                                            v___x_1924_ = lean_box(0);
                                            v_isShared_1925_ = v_isSharedCheck_1933_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_1763_ == 0 {
                                    lean_ctor_set(v___x_1762_, 3, v_r_1760_);
                                    lean_ctor_set(v___x_1762_, 0, v___x_1766_);
                                    v___x_1937_ = v___x_1762_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1766_);
                                    lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_k_1757_);
                                    lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_v_1758_);
                                    lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_r_1760_);
                                    lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_r_1760_);
                                    v___x_1937_ = v_reuseFailAlloc_1938_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        lean_del_object(v___x_1762_);
                        lean_dec(v_v_1758_);
                        lean_dec(v_k_1757_);
                        if lean_obj_tag(v_l_1759_) == 0 {
                            if lean_obj_tag(v_r_1760_) == 0 {
                                v_size_1939_ = lean_ctor_get(v_l_1759_, 0);
                                v_k_1940_ = lean_ctor_get(v_l_1759_, 1);
                                v_v_1941_ = lean_ctor_get(v_l_1759_, 2);
                                v_l_1942_ = lean_ctor_get(v_l_1759_, 3);
                                v_r_1943_ = lean_ctor_get(v_l_1759_, 4);
                                lean_inc(v_r_1943_);
                                v_size_1944_ = lean_ctor_get(v_r_1760_, 0);
                                v_k_1945_ = lean_ctor_get(v_r_1760_, 1);
                                v_v_1946_ = lean_ctor_get(v_r_1760_, 2);
                                v_l_1947_ = lean_ctor_get(v_r_1760_, 3);
                                lean_inc(v_l_1947_);
                                v_r_1948_ = lean_ctor_get(v_r_1760_, 4);
                                v___x_1949_ = lean_unsigned_to_nat(1);
                                v___x_1950_ = lean_nat_dec_lt(v_size_1939_, v_size_1944_);
                                if v___x_1950_ == 0 {
                                    lean_inc(v_l_1942_);
                                    lean_inc(v_v_1941_);
                                    lean_inc(v_k_1940_);
                                    v_isSharedCheck_2086_ = (!lean_is_exclusive(v_l_1759_)) as u8;
                                    if v_isSharedCheck_2086_ == 0 {
                                        v_unused_2087_ = lean_ctor_get(v_l_1759_, 4);
                                        lean_dec(v_unused_2087_);
                                        v_unused_2088_ = lean_ctor_get(v_l_1759_, 3);
                                        lean_dec(v_unused_2088_);
                                        v_unused_2089_ = lean_ctor_get(v_l_1759_, 2);
                                        lean_dec(v_unused_2089_);
                                        v_unused_2090_ = lean_ctor_get(v_l_1759_, 1);
                                        lean_dec(v_unused_2090_);
                                        v_unused_2091_ = lean_ctor_get(v_l_1759_, 0);
                                        lean_dec(v_unused_2091_);
                                        v___x_1952_ = v_l_1759_;
                                        v_isShared_1953_ = v_isSharedCheck_2086_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v_l_1759_);
                                        v___x_1952_ = lean_box(0);
                                        v_isShared_1953_ = v_isSharedCheck_2086_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_1948_);
                                    lean_inc(v_v_1946_);
                                    lean_inc(v_k_1945_);
                                    v_isSharedCheck_2244_ = (!lean_is_exclusive(v_r_1760_)) as u8;
                                    if v_isSharedCheck_2244_ == 0 {
                                        v_unused_2245_ = lean_ctor_get(v_r_1760_, 4);
                                        lean_dec(v_unused_2245_);
                                        v_unused_2246_ = lean_ctor_get(v_r_1760_, 3);
                                        lean_dec(v_unused_2246_);
                                        v_unused_2247_ = lean_ctor_get(v_r_1760_, 2);
                                        lean_dec(v_unused_2247_);
                                        v_unused_2248_ = lean_ctor_get(v_r_1760_, 1);
                                        lean_dec(v_unused_2248_);
                                        v_unused_2249_ = lean_ctor_get(v_r_1760_, 0);
                                        lean_dec(v_unused_2249_);
                                        v___x_2093_ = v_r_1760_;
                                        v_isShared_2094_ = v_isSharedCheck_2244_;
                                        state = 51;
                                        continue;
                                    } else {
                                        lean_dec(v_r_1760_);
                                        v___x_2093_ = lean_box(0);
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
                        v___x_2251_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_2250_) == 0 {
                            if lean_obj_tag(v_l_1759_) == 0 {
                                v_size_2252_ = lean_ctor_get(v_impl_2250_, 0);
                                lean_inc(v_size_2252_);
                                v_size_2253_ = lean_ctor_get(v_l_1759_, 0);
                                v_k_2254_ = lean_ctor_get(v_l_1759_, 1);
                                v_v_2255_ = lean_ctor_get(v_l_1759_, 2);
                                v_l_2256_ = lean_ctor_get(v_l_1759_, 3);
                                v_r_2257_ = lean_ctor_get(v_l_1759_, 4);
                                lean_inc(v_r_2257_);
                                v___x_2258_ = lean_unsigned_to_nat(3);
                                v___x_2259_ = lean_nat_mul(v___x_2258_, v_size_2252_);
                                v___x_2260_ = lean_nat_dec_lt(v___x_2259_, v_size_2253_);
                                lean_dec(v___x_2259_);
                                if v___x_2260_ == 0 {
                                    lean_dec(v_r_2257_);
                                    v___x_2261_ = lean_nat_add(v___x_2251_, v_size_2253_);
                                    v___x_2262_ = lean_nat_add(v___x_2261_, v_size_2252_);
                                    lean_dec(v_size_2252_);
                                    lean_dec(v___x_2261_);
                                    if v_isShared_1763_ == 0 {
                                        lean_ctor_set(v___x_1762_, 4, v_impl_2250_);
                                        lean_ctor_set(v___x_1762_, 0, v___x_2262_);
                                        v___x_2264_ = v___x_1762_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
                                        lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_1757_);
                                        lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_1758_);
                                        lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_l_1759_);
                                        lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_impl_2250_);
                                        v___x_2264_ = v_reuseFailAlloc_2265_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_l_2256_);
                                    lean_inc(v_v_2255_);
                                    lean_inc(v_k_2254_);
                                    lean_inc(v_size_2253_);
                                    v_isSharedCheck_2331_ = (!lean_is_exclusive(v_l_1759_)) as u8;
                                    if v_isSharedCheck_2331_ == 0 {
                                        v_unused_2332_ = lean_ctor_get(v_l_1759_, 4);
                                        lean_dec(v_unused_2332_);
                                        v_unused_2333_ = lean_ctor_get(v_l_1759_, 3);
                                        lean_dec(v_unused_2333_);
                                        v_unused_2334_ = lean_ctor_get(v_l_1759_, 2);
                                        lean_dec(v_unused_2334_);
                                        v_unused_2335_ = lean_ctor_get(v_l_1759_, 1);
                                        lean_dec(v_unused_2335_);
                                        v_unused_2336_ = lean_ctor_get(v_l_1759_, 0);
                                        lean_dec(v_unused_2336_);
                                        v___x_2267_ = v_l_1759_;
                                        v_isShared_2268_ = v_isSharedCheck_2331_;
                                        state = 75;
                                        continue;
                                    } else {
                                        lean_dec(v_l_1759_);
                                        v___x_2267_ = lean_box(0);
                                        v_isShared_2268_ = v_isSharedCheck_2331_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2337_ = lean_ctor_get(v_impl_2250_, 0);
                                lean_inc(v_size_2337_);
                                v___x_2338_ = lean_nat_add(v___x_2251_, v_size_2337_);
                                lean_dec(v_size_2337_);
                                if v_isShared_1763_ == 0 {
                                    lean_ctor_set(v___x_1762_, 4, v_impl_2250_);
                                    lean_ctor_set(v___x_1762_, 0, v___x_2338_);
                                    v___x_2340_ = v___x_1762_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
                                    lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_k_1757_);
                                    lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_v_1758_);
                                    lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_l_1759_);
                                    lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_impl_2250_);
                                    v___x_2340_ = v_reuseFailAlloc_2341_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_l_1759_) == 0 {
                                v_l_2342_ = lean_ctor_get(v_l_1759_, 3);
                                if lean_obj_tag(v_l_2342_) == 0 {
                                    lean_inc_ref(v_l_2342_);
                                    v_r_2343_ = lean_ctor_get(v_l_1759_, 4);
                                    lean_inc(v_r_2343_);
                                    if lean_obj_tag(v_r_2343_) == 0 {
                                        v_size_2344_ = lean_ctor_get(v_l_1759_, 0);
                                        v_k_2345_ = lean_ctor_get(v_l_1759_, 1);
                                        v_v_2346_ = lean_ctor_get(v_l_1759_, 2);
                                        v_isSharedCheck_2359_ =
                                            (!lean_is_exclusive(v_l_1759_)) as u8;
                                        if v_isSharedCheck_2359_ == 0 {
                                            v_unused_2360_ = lean_ctor_get(v_l_1759_, 4);
                                            lean_dec(v_unused_2360_);
                                            v_unused_2361_ = lean_ctor_get(v_l_1759_, 3);
                                            lean_dec(v_unused_2361_);
                                            v___x_2348_ = v_l_1759_;
                                            v_isShared_2349_ = v_isSharedCheck_2359_;
                                            state = 86;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2346_);
                                            lean_inc(v_k_2345_);
                                            lean_inc(v_size_2344_);
                                            lean_dec(v_l_1759_);
                                            v___x_2348_ = lean_box(0);
                                            v_isShared_2349_ = v_isSharedCheck_2359_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_2362_ = lean_ctor_get(v_l_1759_, 1);
                                        v_v_2363_ = lean_ctor_get(v_l_1759_, 2);
                                        v_isSharedCheck_2374_ =
                                            (!lean_is_exclusive(v_l_1759_)) as u8;
                                        if v_isSharedCheck_2374_ == 0 {
                                            v_unused_2375_ = lean_ctor_get(v_l_1759_, 4);
                                            lean_dec(v_unused_2375_);
                                            v_unused_2376_ = lean_ctor_get(v_l_1759_, 3);
                                            lean_dec(v_unused_2376_);
                                            v_unused_2377_ = lean_ctor_get(v_l_1759_, 0);
                                            lean_dec(v_unused_2377_);
                                            v___x_2365_ = v_l_1759_;
                                            v_isShared_2366_ = v_isSharedCheck_2374_;
                                            state = 89;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2363_);
                                            lean_inc(v_k_2362_);
                                            lean_dec(v_l_1759_);
                                            v___x_2365_ = lean_box(0);
                                            v_isShared_2366_ = v_isSharedCheck_2374_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2378_ = lean_ctor_get(v_l_1759_, 4);
                                    lean_inc(v_r_2378_);
                                    if lean_obj_tag(v_r_2378_) == 0 {
                                        lean_inc(v_l_2342_);
                                        v_k_2379_ = lean_ctor_get(v_l_1759_, 1);
                                        v_v_2380_ = lean_ctor_get(v_l_1759_, 2);
                                        v_isSharedCheck_2403_ =
                                            (!lean_is_exclusive(v_l_1759_)) as u8;
                                        if v_isSharedCheck_2403_ == 0 {
                                            v_unused_2404_ = lean_ctor_get(v_l_1759_, 4);
                                            lean_dec(v_unused_2404_);
                                            v_unused_2405_ = lean_ctor_get(v_l_1759_, 3);
                                            lean_dec(v_unused_2405_);
                                            v_unused_2406_ = lean_ctor_get(v_l_1759_, 0);
                                            lean_dec(v_unused_2406_);
                                            v___x_2382_ = v_l_1759_;
                                            v_isShared_2383_ = v_isSharedCheck_2403_;
                                            state = 92;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2380_);
                                            lean_inc(v_k_2379_);
                                            lean_dec(v_l_1759_);
                                            v___x_2382_ = lean_box(0);
                                            v_isShared_2383_ = v_isSharedCheck_2403_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_2407_ = lean_unsigned_to_nat(2);
                                        if v_isShared_1763_ == 0 {
                                            lean_ctor_set(v___x_1762_, 4, v_r_2378_);
                                            lean_ctor_set(v___x_1762_, 0, v___x_2407_);
                                            v___x_2409_ = v___x_1762_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2410_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
                                            lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_k_1757_);
                                            lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_v_1758_);
                                            lean_ctor_set(v_reuseFailAlloc_2410_, 3, v_l_1759_);
                                            lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_r_2378_);
                                            v___x_2409_ = v_reuseFailAlloc_2410_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_1763_ == 0 {
                                    lean_ctor_set(v___x_1762_, 4, v_l_1759_);
                                    lean_ctor_set(v___x_1762_, 0, v___x_2251_);
                                    v___x_2412_ = v___x_1762_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2251_);
                                    lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_k_1757_);
                                    lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_v_1758_);
                                    lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_l_1759_);
                                    lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_l_1759_);
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
                v_size_1784_ = lean_ctor_get(v_l_1771_, 0);
                v_k_1785_ = lean_ctor_get(v_l_1771_, 1);
                v_v_1786_ = lean_ctor_get(v_l_1771_, 2);
                v_l_1787_ = lean_ctor_get(v_l_1771_, 3);
                v_r_1788_ = lean_ctor_get(v_l_1771_, 4);
                v_size_1789_ = lean_ctor_get(v_r_1772_, 0);
                v___x_1790_ = lean_unsigned_to_nat(2);
                v___x_1791_ = lean_nat_mul(v___x_1790_, v_size_1789_);
                v___x_1792_ = lean_nat_dec_lt(v_size_1784_, v___x_1791_);
                lean_dec(v___x_1791_);
                if v___x_1792_ == 0 {
                    lean_inc(v_r_1788_);
                    lean_inc(v_l_1787_);
                    lean_inc(v_v_1786_);
                    lean_inc(v_k_1785_);
                    v_isSharedCheck_1820_ = (!lean_is_exclusive(v_l_1771_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v_unused_1821_ = lean_ctor_get(v_l_1771_, 4);
                        lean_dec(v_unused_1821_);
                        v_unused_1822_ = lean_ctor_get(v_l_1771_, 3);
                        lean_dec(v_unused_1822_);
                        v_unused_1823_ = lean_ctor_get(v_l_1771_, 2);
                        lean_dec(v_unused_1823_);
                        v_unused_1824_ = lean_ctor_get(v_l_1771_, 1);
                        lean_dec(v_unused_1824_);
                        v_unused_1825_ = lean_ctor_get(v_l_1771_, 0);
                        lean_dec(v_unused_1825_);
                        v___x_1794_ = v_l_1771_;
                        v_isShared_1795_ = v_isSharedCheck_1820_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_1771_);
                        v___x_1794_ = lean_box(0);
                        v_isShared_1795_ = v_isSharedCheck_1820_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1762_);
                    v___x_1826_ = lean_nat_add(v___x_1766_, v_size_1767_);
                    lean_dec(v_size_1767_);
                    v___x_1827_ = lean_nat_add(v___x_1826_, v_size_1768_);
                    lean_dec(v_size_1768_);
                    v___x_1828_ = lean_nat_add(v___x_1826_, v_size_1784_);
                    lean_dec(v___x_1826_);
                    lean_inc_ref(v_impl_1765_);
                    if v_isShared_1783_ == 0 {
                        lean_ctor_set(v___x_1782_, 4, v_l_1771_);
                        lean_ctor_set(v___x_1782_, 3, v_impl_1765_);
                        lean_ctor_set(v___x_1782_, 2, v_v_1758_);
                        lean_ctor_set(v___x_1782_, 1, v_k_1757_);
                        lean_ctor_set(v___x_1782_, 0, v___x_1828_);
                        v___x_1830_ = v___x_1782_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1828_);
                        lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_k_1757_);
                        lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_v_1758_);
                        lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_impl_1765_);
                        lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_l_1771_);
                        v___x_1830_ = v_reuseFailAlloc_1843_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1796_ = lean_nat_add(v___x_1766_, v_size_1767_);
                lean_dec(v_size_1767_);
                v___x_1797_ = lean_nat_add(v___x_1796_, v_size_1768_);
                lean_dec(v_size_1768_);
                if lean_obj_tag(v_l_1787_) == 0 {
                    v_size_1818_ = lean_ctor_get(v_l_1787_, 0);
                    lean_inc(v_size_1818_);
                    v___y_1810_ = v_size_1818_;
                    state = 8;
                    continue;
                } else {
                    v___x_1819_ = lean_unsigned_to_nat(0);
                    v___y_1810_ = v___x_1819_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1802_ = lean_nat_add(v___y_1800_, v___y_1801_);
                lean_dec(v___y_1801_);
                lean_dec(v___y_1800_);
                if v_isShared_1795_ == 0 {
                    lean_ctor_set(v___x_1794_, 4, v_r_1772_);
                    lean_ctor_set(v___x_1794_, 3, v_r_1788_);
                    lean_ctor_set(v___x_1794_, 2, v_v_1770_);
                    lean_ctor_set(v___x_1794_, 1, v_k_1769_);
                    lean_ctor_set(v___x_1794_, 0, v___x_1802_);
                    v___x_1804_ = v___x_1794_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1802_);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_k_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_v_1770_);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_r_1788_);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_r_1772_);
                    v___x_1804_ = v_reuseFailAlloc_1808_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1783_ == 0 {
                    lean_ctor_set(v___x_1782_, 4, v___x_1804_);
                    lean_ctor_set(v___x_1782_, 3, v___y_1799_);
                    lean_ctor_set(v___x_1782_, 2, v_v_1786_);
                    lean_ctor_set(v___x_1782_, 1, v_k_1785_);
                    lean_ctor_set(v___x_1782_, 0, v___x_1797_);
                    v___x_1806_ = v___x_1782_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1797_);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_k_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_v_1786_);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 3, v___y_1799_);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 4, v___x_1804_);
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
                lean_dec(v___y_1810_);
                lean_dec(v___x_1796_);
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v_l_1787_);
                    lean_ctor_set(v___x_1762_, 3, v_impl_1765_);
                    lean_ctor_set(v___x_1762_, 0, v___x_1811_);
                    v___x_1813_ = v___x_1762_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1811_);
                    lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_impl_1765_);
                    lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_l_1787_);
                    v___x_1813_ = v_reuseFailAlloc_1817_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1814_ = lean_nat_add(v___x_1766_, v_size_1789_);
                if lean_obj_tag(v_r_1788_) == 0 {
                    v_size_1815_ = lean_ctor_get(v_r_1788_, 0);
                    lean_inc(v_size_1815_);
                    v___y_1799_ = v___x_1813_;
                    v___y_1800_ = v___x_1814_;
                    v___y_1801_ = v_size_1815_;
                    state = 5;
                    continue;
                } else {
                    v___x_1816_ = lean_unsigned_to_nat(0);
                    v___y_1799_ = v___x_1813_;
                    v___y_1800_ = v___x_1814_;
                    v___y_1801_ = v___x_1816_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1837_ = (!lean_is_exclusive(v_impl_1765_)) as u8;
                if v_isSharedCheck_1837_ == 0 {
                    v_unused_1838_ = lean_ctor_get(v_impl_1765_, 4);
                    lean_dec(v_unused_1838_);
                    v_unused_1839_ = lean_ctor_get(v_impl_1765_, 3);
                    lean_dec(v_unused_1839_);
                    v_unused_1840_ = lean_ctor_get(v_impl_1765_, 2);
                    lean_dec(v_unused_1840_);
                    v_unused_1841_ = lean_ctor_get(v_impl_1765_, 1);
                    lean_dec(v_unused_1841_);
                    v_unused_1842_ = lean_ctor_get(v_impl_1765_, 0);
                    lean_dec(v_unused_1842_);
                    v___x_1832_ = v_impl_1765_;
                    v_isShared_1833_ = v_isSharedCheck_1837_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_impl_1765_);
                    v___x_1832_ = lean_box(0);
                    v_isShared_1833_ = v_isSharedCheck_1837_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1833_ == 0 {
                    lean_ctor_set(v___x_1832_, 4, v_r_1772_);
                    lean_ctor_set(v___x_1832_, 3, v___x_1830_);
                    lean_ctor_set(v___x_1832_, 2, v_v_1770_);
                    lean_ctor_set(v___x_1832_, 1, v_k_1769_);
                    lean_ctor_set(v___x_1832_, 0, v___x_1827_);
                    v___x_1835_ = v___x_1832_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1827_);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_k_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_v_1770_);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 3, v___x_1830_);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 4, v_r_1772_);
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
                v_size_1863_ = lean_ctor_get(v_l_1855_, 0);
                v___x_1864_ = lean_nat_add(v___x_1766_, v_size_1857_);
                lean_dec(v_size_1857_);
                v___x_1865_ = lean_nat_add(v___x_1766_, v_size_1863_);
                if v_isShared_1862_ == 0 {
                    lean_ctor_set(v___x_1861_, 4, v_l_1855_);
                    lean_ctor_set(v___x_1861_, 3, v_impl_1765_);
                    lean_ctor_set(v___x_1861_, 2, v_v_1758_);
                    lean_ctor_set(v___x_1861_, 1, v_k_1757_);
                    lean_ctor_set(v___x_1861_, 0, v___x_1865_);
                    v___x_1867_ = v___x_1861_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1865_);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_impl_1765_);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_l_1855_);
                    v___x_1867_ = v_reuseFailAlloc_1871_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v_r_1856_);
                    lean_ctor_set(v___x_1762_, 3, v___x_1867_);
                    lean_ctor_set(v___x_1762_, 2, v_v_1859_);
                    lean_ctor_set(v___x_1762_, 1, v_k_1858_);
                    lean_ctor_set(v___x_1762_, 0, v___x_1864_);
                    v___x_1869_ = v___x_1762_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1864_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_k_1858_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_v_1859_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 3, v___x_1867_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 4, v_r_1856_);
                    v___x_1869_ = v_reuseFailAlloc_1870_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1869_;
            }
            17 => {
                v_k_1880_ = lean_ctor_get(v_l_1855_, 1);
                v_v_1881_ = lean_ctor_get(v_l_1855_, 2);
                v_isSharedCheck_1895_ = (!lean_is_exclusive(v_l_1855_)) as u8;
                if v_isSharedCheck_1895_ == 0 {
                    v_unused_1896_ = lean_ctor_get(v_l_1855_, 4);
                    lean_dec(v_unused_1896_);
                    v_unused_1897_ = lean_ctor_get(v_l_1855_, 3);
                    lean_dec(v_unused_1897_);
                    v_unused_1898_ = lean_ctor_get(v_l_1855_, 0);
                    lean_dec(v_unused_1898_);
                    v___x_1883_ = v_l_1855_;
                    v_isShared_1884_ = v_isSharedCheck_1895_;
                    state = 18;
                    continue;
                } else {
                    lean_inc(v_v_1881_);
                    lean_inc(v_k_1880_);
                    lean_dec(v_l_1855_);
                    v___x_1883_ = lean_box(0);
                    v_isShared_1884_ = v_isSharedCheck_1895_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1885_ = lean_unsigned_to_nat(3);
                if v_isShared_1884_ == 0 {
                    lean_ctor_set(v___x_1883_, 4, v_r_1856_);
                    lean_ctor_set(v___x_1883_, 3, v_r_1856_);
                    lean_ctor_set(v___x_1883_, 2, v_v_1758_);
                    lean_ctor_set(v___x_1883_, 1, v_k_1757_);
                    lean_ctor_set(v___x_1883_, 0, v___x_1766_);
                    v___x_1887_ = v___x_1883_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1766_);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_r_1856_);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_r_1856_);
                    v___x_1887_ = v_reuseFailAlloc_1894_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1879_ == 0 {
                    lean_ctor_set(v___x_1878_, 3, v_r_1856_);
                    lean_ctor_set(v___x_1878_, 0, v___x_1766_);
                    v___x_1889_ = v___x_1878_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1766_);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_k_1875_);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_v_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_r_1856_);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 4, v_r_1856_);
                    v___x_1889_ = v_reuseFailAlloc_1893_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v___x_1889_);
                    lean_ctor_set(v___x_1762_, 3, v___x_1887_);
                    lean_ctor_set(v___x_1762_, 2, v_v_1881_);
                    lean_ctor_set(v___x_1762_, 1, v_k_1880_);
                    lean_ctor_set(v___x_1762_, 0, v___x_1885_);
                    v___x_1891_ = v___x_1762_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1880_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1881_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 3, v___x_1887_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 4, v___x_1889_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1891_;
            }
            22 => {
                v___x_1909_ = lean_unsigned_to_nat(3);
                if v_isShared_1908_ == 0 {
                    lean_ctor_set(v___x_1907_, 4, v_l_1855_);
                    lean_ctor_set(v___x_1907_, 2, v_v_1758_);
                    lean_ctor_set(v___x_1907_, 1, v_k_1757_);
                    lean_ctor_set(v___x_1907_, 0, v___x_1766_);
                    v___x_1911_ = v___x_1907_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1766_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_l_1855_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_l_1855_);
                    v___x_1911_ = v_reuseFailAlloc_1915_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v_r_1903_);
                    lean_ctor_set(v___x_1762_, 3, v___x_1911_);
                    lean_ctor_set(v___x_1762_, 2, v_v_1905_);
                    lean_ctor_set(v___x_1762_, 1, v_k_1904_);
                    lean_ctor_set(v___x_1762_, 0, v___x_1909_);
                    v___x_1913_ = v___x_1762_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1909_);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_k_1904_);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_v_1905_);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 3, v___x_1911_);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_r_1903_);
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
                    lean_ctor_set(v___x_1924_, 3, v_r_1903_);
                    v___x_1927_ = v___x_1924_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_size_1920_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1921_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1922_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_r_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_r_1903_);
                    v___x_1927_ = v_reuseFailAlloc_1932_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_1928_ = lean_unsigned_to_nat(2);
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v___x_1927_);
                    lean_ctor_set(v___x_1762_, 3, v_r_1903_);
                    lean_ctor_set(v___x_1762_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1762_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_r_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 4, v___x_1927_);
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
                v_tree_1955_ = lean_ctor_get(v___x_1954_, 2);
                lean_inc(v_tree_1955_);
                if lean_obj_tag(v_tree_1955_) == 0 {
                    v_k_1956_ = lean_ctor_get(v___x_1954_, 0);
                    lean_inc(v_k_1956_);
                    v_v_1957_ = lean_ctor_get(v___x_1954_, 1);
                    lean_inc(v_v_1957_);
                    lean_dec_ref(v___x_1954_);
                    v_size_1958_ = lean_ctor_get(v_tree_1955_, 0);
                    v___x_1959_ = lean_unsigned_to_nat(3);
                    v___x_1960_ = lean_nat_mul(v___x_1959_, v_size_1958_);
                    v___x_1961_ = lean_nat_dec_lt(v___x_1960_, v_size_1944_);
                    lean_dec(v___x_1960_);
                    if v___x_1961_ == 0 {
                        lean_dec(v_l_1947_);
                        v___x_1962_ = lean_nat_add(v___x_1949_, v_size_1958_);
                        v___x_1963_ = lean_nat_add(v___x_1962_, v_size_1944_);
                        lean_dec(v___x_1962_);
                        if v_isShared_1953_ == 0 {
                            lean_ctor_set(v___x_1952_, 4, v_r_1760_);
                            lean_ctor_set(v___x_1952_, 3, v_tree_1955_);
                            lean_ctor_set(v___x_1952_, 2, v_v_1957_);
                            lean_ctor_set(v___x_1952_, 1, v_k_1956_);
                            lean_ctor_set(v___x_1952_, 0, v___x_1963_);
                            v___x_1965_ = v___x_1952_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
                            lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_k_1956_);
                            lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_v_1957_);
                            lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_tree_1955_);
                            lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_r_1760_);
                            v___x_1965_ = v_reuseFailAlloc_1966_;
                            state = 30;
                            continue;
                        }
                    } else {
                        lean_inc(v_r_1948_);
                        lean_inc(v_v_1946_);
                        lean_inc(v_k_1945_);
                        lean_inc(v_size_1944_);
                        v_isSharedCheck_2021_ = (!lean_is_exclusive(v_r_1760_)) as u8;
                        if v_isSharedCheck_2021_ == 0 {
                            v_unused_2022_ = lean_ctor_get(v_r_1760_, 4);
                            lean_dec(v_unused_2022_);
                            v_unused_2023_ = lean_ctor_get(v_r_1760_, 3);
                            lean_dec(v_unused_2023_);
                            v_unused_2024_ = lean_ctor_get(v_r_1760_, 2);
                            lean_dec(v_unused_2024_);
                            v_unused_2025_ = lean_ctor_get(v_r_1760_, 1);
                            lean_dec(v_unused_2025_);
                            v_unused_2026_ = lean_ctor_get(v_r_1760_, 0);
                            lean_dec(v_unused_2026_);
                            v___x_1968_ = v_r_1760_;
                            v_isShared_1969_ = v_isSharedCheck_2021_;
                            state = 31;
                            continue;
                        } else {
                            lean_dec(v_r_1760_);
                            v___x_1968_ = lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_2021_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_r_1948_);
                    lean_inc(v_v_1946_);
                    lean_inc(v_k_1945_);
                    lean_inc(v_size_1944_);
                    v_isSharedCheck_2080_ = (!lean_is_exclusive(v_r_1760_)) as u8;
                    if v_isSharedCheck_2080_ == 0 {
                        v_unused_2081_ = lean_ctor_get(v_r_1760_, 4);
                        lean_dec(v_unused_2081_);
                        v_unused_2082_ = lean_ctor_get(v_r_1760_, 3);
                        lean_dec(v_unused_2082_);
                        v_unused_2083_ = lean_ctor_get(v_r_1760_, 2);
                        lean_dec(v_unused_2083_);
                        v_unused_2084_ = lean_ctor_get(v_r_1760_, 1);
                        lean_dec(v_unused_2084_);
                        v_unused_2085_ = lean_ctor_get(v_r_1760_, 0);
                        lean_dec(v_unused_2085_);
                        v___x_2028_ = v_r_1760_;
                        v_isShared_2029_ = v_isSharedCheck_2080_;
                        state = 40;
                        continue;
                    } else {
                        lean_dec(v_r_1760_);
                        v___x_2028_ = lean_box(0);
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
                v_size_1970_ = lean_ctor_get(v_l_1947_, 0);
                v_k_1971_ = lean_ctor_get(v_l_1947_, 1);
                v_v_1972_ = lean_ctor_get(v_l_1947_, 2);
                v_l_1973_ = lean_ctor_get(v_l_1947_, 3);
                v_r_1974_ = lean_ctor_get(v_l_1947_, 4);
                v_size_1975_ = lean_ctor_get(v_r_1948_, 0);
                v___x_1976_ = lean_unsigned_to_nat(2);
                v___x_1977_ = lean_nat_mul(v___x_1976_, v_size_1975_);
                v___x_1978_ = lean_nat_dec_lt(v_size_1970_, v___x_1977_);
                lean_dec(v___x_1977_);
                if v___x_1978_ == 0 {
                    lean_inc(v_r_1974_);
                    lean_inc(v_l_1973_);
                    lean_inc(v_v_1972_);
                    lean_inc(v_k_1971_);
                    v_isSharedCheck_2006_ = (!lean_is_exclusive(v_l_1947_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v_unused_2007_ = lean_ctor_get(v_l_1947_, 4);
                        lean_dec(v_unused_2007_);
                        v_unused_2008_ = lean_ctor_get(v_l_1947_, 3);
                        lean_dec(v_unused_2008_);
                        v_unused_2009_ = lean_ctor_get(v_l_1947_, 2);
                        lean_dec(v_unused_2009_);
                        v_unused_2010_ = lean_ctor_get(v_l_1947_, 1);
                        lean_dec(v_unused_2010_);
                        v_unused_2011_ = lean_ctor_get(v_l_1947_, 0);
                        lean_dec(v_unused_2011_);
                        v___x_1980_ = v_l_1947_;
                        v_isShared_1981_ = v_isSharedCheck_2006_;
                        state = 32;
                        continue;
                    } else {
                        lean_dec(v_l_1947_);
                        v___x_1980_ = lean_box(0);
                        v_isShared_1981_ = v_isSharedCheck_2006_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_2012_ = lean_nat_add(v___x_1949_, v_size_1958_);
                    v___x_2013_ = lean_nat_add(v___x_2012_, v_size_1944_);
                    lean_dec(v_size_1944_);
                    v___x_2014_ = lean_nat_add(v___x_2012_, v_size_1970_);
                    lean_dec(v___x_2012_);
                    if v_isShared_1969_ == 0 {
                        lean_ctor_set(v___x_1968_, 4, v_l_1947_);
                        lean_ctor_set(v___x_1968_, 3, v_tree_1955_);
                        lean_ctor_set(v___x_1968_, 2, v_v_1957_);
                        lean_ctor_set(v___x_1968_, 1, v_k_1956_);
                        lean_ctor_set(v___x_1968_, 0, v___x_2014_);
                        v___x_2016_ = v___x_1968_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2014_);
                        lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_1956_);
                        lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_1957_);
                        lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_tree_1955_);
                        lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_l_1947_);
                        v___x_2016_ = v_reuseFailAlloc_2020_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_1982_ = lean_nat_add(v___x_1949_, v_size_1958_);
                v___x_1983_ = lean_nat_add(v___x_1982_, v_size_1944_);
                lean_dec(v_size_1944_);
                if lean_obj_tag(v_l_1973_) == 0 {
                    v_size_2004_ = lean_ctor_get(v_l_1973_, 0);
                    lean_inc(v_size_2004_);
                    v___y_1996_ = v_size_2004_;
                    state = 36;
                    continue;
                } else {
                    v___x_2005_ = lean_unsigned_to_nat(0);
                    v___y_1996_ = v___x_2005_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_1988_ = lean_nat_add(v___y_1985_, v___y_1987_);
                lean_dec(v___y_1987_);
                lean_dec(v___y_1985_);
                if v_isShared_1981_ == 0 {
                    lean_ctor_set(v___x_1980_, 4, v_r_1948_);
                    lean_ctor_set(v___x_1980_, 3, v_r_1974_);
                    lean_ctor_set(v___x_1980_, 2, v_v_1946_);
                    lean_ctor_set(v___x_1980_, 1, v_k_1945_);
                    lean_ctor_set(v___x_1980_, 0, v___x_1988_);
                    v___x_1990_ = v___x_1980_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
                    lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1945_);
                    lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1946_);
                    lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_r_1974_);
                    lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_r_1948_);
                    v___x_1990_ = v_reuseFailAlloc_1994_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_1969_ == 0 {
                    lean_ctor_set(v___x_1968_, 4, v___x_1990_);
                    lean_ctor_set(v___x_1968_, 3, v___y_1986_);
                    lean_ctor_set(v___x_1968_, 2, v_v_1972_);
                    lean_ctor_set(v___x_1968_, 1, v_k_1971_);
                    lean_ctor_set(v___x_1968_, 0, v___x_1983_);
                    v___x_1992_ = v___x_1968_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1983_);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1971_);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1972_);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 3, v___y_1986_);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 4, v___x_1990_);
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
                lean_dec(v___y_1996_);
                lean_dec(v___x_1982_);
                if v_isShared_1953_ == 0 {
                    lean_ctor_set(v___x_1952_, 4, v_l_1973_);
                    lean_ctor_set(v___x_1952_, 3, v_tree_1955_);
                    lean_ctor_set(v___x_1952_, 2, v_v_1957_);
                    lean_ctor_set(v___x_1952_, 1, v_k_1956_);
                    lean_ctor_set(v___x_1952_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1952_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1956_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1957_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_tree_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_l_1973_);
                    v___x_1999_ = v_reuseFailAlloc_2003_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_2000_ = lean_nat_add(v___x_1949_, v_size_1975_);
                if lean_obj_tag(v_r_1974_) == 0 {
                    v_size_2001_ = lean_ctor_get(v_r_1974_, 0);
                    lean_inc(v_size_2001_);
                    v___y_1985_ = v___x_2000_;
                    v___y_1986_ = v___x_1999_;
                    v___y_1987_ = v_size_2001_;
                    state = 33;
                    continue;
                } else {
                    v___x_2002_ = lean_unsigned_to_nat(0);
                    v___y_1985_ = v___x_2000_;
                    v___y_1986_ = v___x_1999_;
                    v___y_1987_ = v___x_2002_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_1953_ == 0 {
                    lean_ctor_set(v___x_1952_, 4, v_r_1948_);
                    lean_ctor_set(v___x_1952_, 3, v___x_2016_);
                    lean_ctor_set(v___x_1952_, 2, v_v_1946_);
                    lean_ctor_set(v___x_1952_, 1, v_k_1945_);
                    lean_ctor_set(v___x_1952_, 0, v___x_2013_);
                    v___x_2018_ = v___x_1952_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2013_);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_k_1945_);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_v_1946_);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 3, v___x_2016_);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_r_1948_);
                    v___x_2018_ = v_reuseFailAlloc_2019_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2018_;
            }
            40 => {
                if lean_obj_tag(v_l_1947_) == 0 {
                    if lean_obj_tag(v_r_1948_) == 0 {
                        v_k_2030_ = lean_ctor_get(v___x_1954_, 0);
                        lean_inc(v_k_2030_);
                        v_v_2031_ = lean_ctor_get(v___x_1954_, 1);
                        lean_inc(v_v_2031_);
                        lean_dec_ref(v___x_1954_);
                        v_size_2032_ = lean_ctor_get(v_l_1947_, 0);
                        v___x_2033_ = lean_nat_add(v___x_1949_, v_size_1944_);
                        lean_dec(v_size_1944_);
                        v___x_2034_ = lean_nat_add(v___x_1949_, v_size_2032_);
                        if v_isShared_2029_ == 0 {
                            lean_ctor_set(v___x_2028_, 4, v_l_1947_);
                            lean_ctor_set(v___x_2028_, 3, v_tree_1955_);
                            lean_ctor_set(v___x_2028_, 2, v_v_2031_);
                            lean_ctor_set(v___x_2028_, 1, v_k_2030_);
                            lean_ctor_set(v___x_2028_, 0, v___x_2034_);
                            v___x_2036_ = v___x_2028_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2034_);
                            lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_2030_);
                            lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_2031_);
                            lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_tree_1955_);
                            lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_l_1947_);
                            v___x_2036_ = v_reuseFailAlloc_2040_;
                            state = 41;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_1944_);
                        v_k_2041_ = lean_ctor_get(v___x_1954_, 0);
                        lean_inc(v_k_2041_);
                        v_v_2042_ = lean_ctor_get(v___x_1954_, 1);
                        lean_inc(v_v_2042_);
                        lean_dec_ref(v___x_1954_);
                        v_k_2043_ = lean_ctor_get(v_l_1947_, 1);
                        v_v_2044_ = lean_ctor_get(v_l_1947_, 2);
                        v_isSharedCheck_2058_ = (!lean_is_exclusive(v_l_1947_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v_unused_2059_ = lean_ctor_get(v_l_1947_, 4);
                            lean_dec(v_unused_2059_);
                            v_unused_2060_ = lean_ctor_get(v_l_1947_, 3);
                            lean_dec(v_unused_2060_);
                            v_unused_2061_ = lean_ctor_get(v_l_1947_, 0);
                            lean_dec(v_unused_2061_);
                            v___x_2046_ = v_l_1947_;
                            v_isShared_2047_ = v_isSharedCheck_2058_;
                            state = 43;
                            continue;
                        } else {
                            lean_inc(v_v_2044_);
                            lean_inc(v_k_2043_);
                            lean_dec(v_l_1947_);
                            v___x_2046_ = lean_box(0);
                            v_isShared_2047_ = v_isSharedCheck_2058_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_r_1948_) == 0 {
                        lean_dec(v_size_1944_);
                        v_k_2062_ = lean_ctor_get(v___x_1954_, 0);
                        lean_inc(v_k_2062_);
                        v_v_2063_ = lean_ctor_get(v___x_1954_, 1);
                        lean_inc(v_v_2063_);
                        lean_dec_ref(v___x_1954_);
                        v___x_2064_ = lean_unsigned_to_nat(3);
                        if v_isShared_2029_ == 0 {
                            lean_ctor_set(v___x_2028_, 4, v_l_1947_);
                            lean_ctor_set(v___x_2028_, 2, v_v_2063_);
                            lean_ctor_set(v___x_2028_, 1, v_k_2062_);
                            lean_ctor_set(v___x_2028_, 0, v___x_1949_);
                            v___x_2066_ = v___x_2028_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_1949_);
                            lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_k_2062_);
                            lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_v_2063_);
                            lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_l_1947_);
                            lean_ctor_set(v_reuseFailAlloc_2070_, 4, v_l_1947_);
                            v___x_2066_ = v_reuseFailAlloc_2070_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_2071_ = lean_ctor_get(v___x_1954_, 0);
                        lean_inc(v_k_2071_);
                        v_v_2072_ = lean_ctor_get(v___x_1954_, 1);
                        lean_inc(v_v_2072_);
                        lean_dec_ref(v___x_1954_);
                        if v_isShared_2029_ == 0 {
                            lean_ctor_set(v___x_2028_, 3, v_r_1948_);
                            v___x_2074_ = v___x_2028_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_size_1944_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_1945_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_1946_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_r_1948_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_r_1948_);
                            v___x_2074_ = v_reuseFailAlloc_2079_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_1953_ == 0 {
                    lean_ctor_set(v___x_1952_, 4, v_r_1948_);
                    lean_ctor_set(v___x_1952_, 3, v___x_2036_);
                    lean_ctor_set(v___x_1952_, 2, v_v_1946_);
                    lean_ctor_set(v___x_1952_, 1, v_k_1945_);
                    lean_ctor_set(v___x_1952_, 0, v___x_2033_);
                    v___x_2038_ = v___x_1952_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2033_);
                    lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_k_1945_);
                    lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_v_1946_);
                    lean_ctor_set(v_reuseFailAlloc_2039_, 3, v___x_2036_);
                    lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_r_1948_);
                    v___x_2038_ = v_reuseFailAlloc_2039_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2038_;
            }
            43 => {
                v___x_2048_ = lean_unsigned_to_nat(3);
                if v_isShared_2047_ == 0 {
                    lean_ctor_set(v___x_2046_, 4, v_r_1948_);
                    lean_ctor_set(v___x_2046_, 3, v_r_1948_);
                    lean_ctor_set(v___x_2046_, 2, v_v_2042_);
                    lean_ctor_set(v___x_2046_, 1, v_k_2041_);
                    lean_ctor_set(v___x_2046_, 0, v___x_1949_);
                    v___x_2050_ = v___x_2046_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_2041_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_r_1948_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_r_1948_);
                    v___x_2050_ = v_reuseFailAlloc_2057_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2029_ == 0 {
                    lean_ctor_set(v___x_2028_, 3, v_r_1948_);
                    lean_ctor_set(v___x_2028_, 0, v___x_1949_);
                    v___x_2052_ = v___x_2028_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_k_1945_);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_v_1946_);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_r_1948_);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_r_1948_);
                    v___x_2052_ = v_reuseFailAlloc_2056_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1953_ == 0 {
                    lean_ctor_set(v___x_1952_, 4, v___x_2052_);
                    lean_ctor_set(v___x_1952_, 3, v___x_2050_);
                    lean_ctor_set(v___x_1952_, 2, v_v_2044_);
                    lean_ctor_set(v___x_1952_, 1, v_k_2043_);
                    lean_ctor_set(v___x_1952_, 0, v___x_2048_);
                    v___x_2054_ = v___x_1952_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2048_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_k_2043_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_v_2044_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 3, v___x_2050_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 4, v___x_2052_);
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
                    lean_ctor_set(v___x_1952_, 4, v_r_1948_);
                    lean_ctor_set(v___x_1952_, 3, v___x_2066_);
                    lean_ctor_set(v___x_1952_, 2, v_v_1946_);
                    lean_ctor_set(v___x_1952_, 1, v_k_1945_);
                    lean_ctor_set(v___x_1952_, 0, v___x_2064_);
                    v___x_2068_ = v___x_1952_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2064_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1945_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1946_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 3, v___x_2066_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_r_1948_);
                    v___x_2068_ = v_reuseFailAlloc_2069_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2068_;
            }
            49 => {
                v___x_2075_ = lean_unsigned_to_nat(2);
                if v_isShared_1953_ == 0 {
                    lean_ctor_set(v___x_1952_, 4, v___x_2074_);
                    lean_ctor_set(v___x_1952_, 3, v_r_1948_);
                    lean_ctor_set(v___x_1952_, 2, v_v_2072_);
                    lean_ctor_set(v___x_1952_, 1, v_k_2071_);
                    lean_ctor_set(v___x_1952_, 0, v___x_2075_);
                    v___x_2077_ = v___x_1952_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_2071_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_2072_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_r_1948_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___x_2074_);
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
                v_tree_2096_ = lean_ctor_get(v___x_2095_, 2);
                lean_inc(v_tree_2096_);
                if lean_obj_tag(v_tree_2096_) == 0 {
                    v_k_2097_ = lean_ctor_get(v___x_2095_, 0);
                    lean_inc(v_k_2097_);
                    v_v_2098_ = lean_ctor_get(v___x_2095_, 1);
                    lean_inc(v_v_2098_);
                    lean_dec_ref(v___x_2095_);
                    v_size_2099_ = lean_ctor_get(v_tree_2096_, 0);
                    v___x_2100_ = lean_unsigned_to_nat(3);
                    v___x_2101_ = lean_nat_mul(v___x_2100_, v_size_2099_);
                    v___x_2102_ = lean_nat_dec_lt(v___x_2101_, v_size_1939_);
                    lean_dec(v___x_2101_);
                    if v___x_2102_ == 0 {
                        lean_dec(v_r_1943_);
                        v___x_2103_ = lean_nat_add(v___x_1949_, v_size_1939_);
                        v___x_2104_ = lean_nat_add(v___x_2103_, v_size_2099_);
                        lean_dec(v___x_2103_);
                        if v_isShared_2094_ == 0 {
                            lean_ctor_set(v___x_2093_, 4, v_tree_2096_);
                            lean_ctor_set(v___x_2093_, 3, v_l_1759_);
                            lean_ctor_set(v___x_2093_, 2, v_v_2098_);
                            lean_ctor_set(v___x_2093_, 1, v_k_2097_);
                            lean_ctor_set(v___x_2093_, 0, v___x_2104_);
                            v___x_2106_ = v___x_2093_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
                            lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_k_2097_);
                            lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_v_2098_);
                            lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_l_1759_);
                            lean_ctor_set(v_reuseFailAlloc_2107_, 4, v_tree_2096_);
                            v___x_2106_ = v_reuseFailAlloc_2107_;
                            state = 52;
                            continue;
                        }
                    } else {
                        lean_inc(v_l_1942_);
                        lean_inc(v_v_1941_);
                        lean_inc(v_k_1940_);
                        lean_inc(v_size_1939_);
                        v_isSharedCheck_2173_ = (!lean_is_exclusive(v_l_1759_)) as u8;
                        if v_isSharedCheck_2173_ == 0 {
                            v_unused_2174_ = lean_ctor_get(v_l_1759_, 4);
                            lean_dec(v_unused_2174_);
                            v_unused_2175_ = lean_ctor_get(v_l_1759_, 3);
                            lean_dec(v_unused_2175_);
                            v_unused_2176_ = lean_ctor_get(v_l_1759_, 2);
                            lean_dec(v_unused_2176_);
                            v_unused_2177_ = lean_ctor_get(v_l_1759_, 1);
                            lean_dec(v_unused_2177_);
                            v_unused_2178_ = lean_ctor_get(v_l_1759_, 0);
                            lean_dec(v_unused_2178_);
                            v___x_2109_ = v_l_1759_;
                            v_isShared_2110_ = v_isSharedCheck_2173_;
                            state = 53;
                            continue;
                        } else {
                            lean_dec(v_l_1759_);
                            v___x_2109_ = lean_box(0);
                            v_isShared_2110_ = v_isSharedCheck_2173_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_l_1942_) == 0 {
                        lean_inc_ref(v_l_1942_);
                        lean_inc(v_v_1941_);
                        lean_inc(v_k_1940_);
                        lean_inc(v_size_1939_);
                        v_isSharedCheck_2202_ = (!lean_is_exclusive(v_l_1759_)) as u8;
                        if v_isSharedCheck_2202_ == 0 {
                            v_unused_2203_ = lean_ctor_get(v_l_1759_, 4);
                            lean_dec(v_unused_2203_);
                            v_unused_2204_ = lean_ctor_get(v_l_1759_, 3);
                            lean_dec(v_unused_2204_);
                            v_unused_2205_ = lean_ctor_get(v_l_1759_, 2);
                            lean_dec(v_unused_2205_);
                            v_unused_2206_ = lean_ctor_get(v_l_1759_, 1);
                            lean_dec(v_unused_2206_);
                            v_unused_2207_ = lean_ctor_get(v_l_1759_, 0);
                            lean_dec(v_unused_2207_);
                            v___x_2180_ = v_l_1759_;
                            v_isShared_2181_ = v_isSharedCheck_2202_;
                            state = 63;
                            continue;
                        } else {
                            lean_dec(v_l_1759_);
                            v___x_2180_ = lean_box(0);
                            v_isShared_2181_ = v_isSharedCheck_2202_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_r_1943_) == 0 {
                            lean_inc(v_l_1942_);
                            lean_inc(v_v_1941_);
                            lean_inc(v_k_1940_);
                            v_isSharedCheck_2232_ = (!lean_is_exclusive(v_l_1759_)) as u8;
                            if v_isSharedCheck_2232_ == 0 {
                                v_unused_2233_ = lean_ctor_get(v_l_1759_, 4);
                                lean_dec(v_unused_2233_);
                                v_unused_2234_ = lean_ctor_get(v_l_1759_, 3);
                                lean_dec(v_unused_2234_);
                                v_unused_2235_ = lean_ctor_get(v_l_1759_, 2);
                                lean_dec(v_unused_2235_);
                                v_unused_2236_ = lean_ctor_get(v_l_1759_, 1);
                                lean_dec(v_unused_2236_);
                                v_unused_2237_ = lean_ctor_get(v_l_1759_, 0);
                                lean_dec(v_unused_2237_);
                                v___x_2209_ = v_l_1759_;
                                v_isShared_2210_ = v_isSharedCheck_2232_;
                                state = 68;
                                continue;
                            } else {
                                lean_dec(v_l_1759_);
                                v___x_2209_ = lean_box(0);
                                v_isShared_2210_ = v_isSharedCheck_2232_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_2238_ = lean_ctor_get(v___x_2095_, 0);
                            lean_inc(v_k_2238_);
                            v_v_2239_ = lean_ctor_get(v___x_2095_, 1);
                            lean_inc(v_v_2239_);
                            lean_dec_ref(v___x_2095_);
                            v___x_2240_ = lean_unsigned_to_nat(2);
                            if v_isShared_2094_ == 0 {
                                lean_ctor_set(v___x_2093_, 4, v_r_1943_);
                                lean_ctor_set(v___x_2093_, 3, v_l_1759_);
                                lean_ctor_set(v___x_2093_, 2, v_v_2239_);
                                lean_ctor_set(v___x_2093_, 1, v_k_2238_);
                                lean_ctor_set(v___x_2093_, 0, v___x_2240_);
                                v___x_2242_ = v___x_2093_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
                                lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_k_2238_);
                                lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_v_2239_);
                                lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_l_1759_);
                                lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_r_1943_);
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
                v_size_2111_ = lean_ctor_get(v_l_1942_, 0);
                v_size_2112_ = lean_ctor_get(v_r_1943_, 0);
                v_k_2113_ = lean_ctor_get(v_r_1943_, 1);
                v_v_2114_ = lean_ctor_get(v_r_1943_, 2);
                v_l_2115_ = lean_ctor_get(v_r_1943_, 3);
                v_r_2116_ = lean_ctor_get(v_r_1943_, 4);
                v___x_2117_ = lean_unsigned_to_nat(2);
                v___x_2118_ = lean_nat_mul(v___x_2117_, v_size_2111_);
                v___x_2119_ = lean_nat_dec_lt(v_size_2112_, v___x_2118_);
                lean_dec(v___x_2118_);
                if v___x_2119_ == 0 {
                    lean_inc(v_r_2116_);
                    lean_inc(v_l_2115_);
                    lean_inc(v_v_2114_);
                    lean_inc(v_k_2113_);
                    lean_del_object(v___x_2109_);
                    v_isSharedCheck_2157_ = (!lean_is_exclusive(v_r_1943_)) as u8;
                    if v_isSharedCheck_2157_ == 0 {
                        v_unused_2158_ = lean_ctor_get(v_r_1943_, 4);
                        lean_dec(v_unused_2158_);
                        v_unused_2159_ = lean_ctor_get(v_r_1943_, 3);
                        lean_dec(v_unused_2159_);
                        v_unused_2160_ = lean_ctor_get(v_r_1943_, 2);
                        lean_dec(v_unused_2160_);
                        v_unused_2161_ = lean_ctor_get(v_r_1943_, 1);
                        lean_dec(v_unused_2161_);
                        v_unused_2162_ = lean_ctor_get(v_r_1943_, 0);
                        lean_dec(v_unused_2162_);
                        v___x_2121_ = v_r_1943_;
                        v_isShared_2122_ = v_isSharedCheck_2157_;
                        state = 54;
                        continue;
                    } else {
                        lean_dec(v_r_1943_);
                        v___x_2121_ = lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2157_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_2163_ = lean_nat_add(v___x_1949_, v_size_1939_);
                    lean_dec(v_size_1939_);
                    v___x_2164_ = lean_nat_add(v___x_2163_, v_size_2099_);
                    lean_dec(v___x_2163_);
                    v___x_2165_ = lean_nat_add(v___x_1949_, v_size_2099_);
                    v___x_2166_ = lean_nat_add(v___x_2165_, v_size_2112_);
                    lean_dec(v___x_2165_);
                    if v_isShared_2094_ == 0 {
                        lean_ctor_set(v___x_2093_, 4, v_tree_2096_);
                        lean_ctor_set(v___x_2093_, 3, v_r_1943_);
                        lean_ctor_set(v___x_2093_, 2, v_v_2098_);
                        lean_ctor_set(v___x_2093_, 1, v_k_2097_);
                        lean_ctor_set(v___x_2093_, 0, v___x_2166_);
                        v___x_2168_ = v___x_2093_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2166_);
                        lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2097_);
                        lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2098_);
                        lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_1943_);
                        lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_tree_2096_);
                        v___x_2168_ = v_reuseFailAlloc_2172_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_2123_ = lean_nat_add(v___x_1949_, v_size_1939_);
                lean_dec(v_size_1939_);
                v___x_2124_ = lean_nat_add(v___x_2123_, v_size_2099_);
                lean_dec(v___x_2123_);
                v___x_2145_ = lean_nat_add(v___x_1949_, v_size_2111_);
                if lean_obj_tag(v_l_2115_) == 0 {
                    v_size_2155_ = lean_ctor_get(v_l_2115_, 0);
                    lean_inc(v_size_2155_);
                    v___y_2147_ = v_size_2155_;
                    state = 59;
                    continue;
                } else {
                    v___x_2156_ = lean_unsigned_to_nat(0);
                    v___y_2147_ = v___x_2156_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_2129_ = lean_nat_add(v___y_2126_, v___y_2128_);
                lean_dec(v___y_2128_);
                lean_dec(v___y_2126_);
                lean_inc_ref(v_tree_2096_);
                if v_isShared_2122_ == 0 {
                    lean_ctor_set(v___x_2121_, 4, v_tree_2096_);
                    lean_ctor_set(v___x_2121_, 3, v_r_2116_);
                    lean_ctor_set(v___x_2121_, 2, v_v_2098_);
                    lean_ctor_set(v___x_2121_, 1, v_k_2097_);
                    lean_ctor_set(v___x_2121_, 0, v___x_2129_);
                    v___x_2131_ = v___x_2121_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2129_);
                    lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2097_);
                    lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2098_);
                    lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_r_2116_);
                    lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_tree_2096_);
                    v___x_2131_ = v_reuseFailAlloc_2144_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_2138_ = (!lean_is_exclusive(v_tree_2096_)) as u8;
                if v_isSharedCheck_2138_ == 0 {
                    v_unused_2139_ = lean_ctor_get(v_tree_2096_, 4);
                    lean_dec(v_unused_2139_);
                    v_unused_2140_ = lean_ctor_get(v_tree_2096_, 3);
                    lean_dec(v_unused_2140_);
                    v_unused_2141_ = lean_ctor_get(v_tree_2096_, 2);
                    lean_dec(v_unused_2141_);
                    v_unused_2142_ = lean_ctor_get(v_tree_2096_, 1);
                    lean_dec(v_unused_2142_);
                    v_unused_2143_ = lean_ctor_get(v_tree_2096_, 0);
                    lean_dec(v_unused_2143_);
                    v___x_2133_ = v_tree_2096_;
                    v_isShared_2134_ = v_isSharedCheck_2138_;
                    state = 57;
                    continue;
                } else {
                    lean_dec(v_tree_2096_);
                    v___x_2133_ = lean_box(0);
                    v_isShared_2134_ = v_isSharedCheck_2138_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2134_ == 0 {
                    lean_ctor_set(v___x_2133_, 4, v___x_2131_);
                    lean_ctor_set(v___x_2133_, 3, v___y_2127_);
                    lean_ctor_set(v___x_2133_, 2, v_v_2114_);
                    lean_ctor_set(v___x_2133_, 1, v_k_2113_);
                    lean_ctor_set(v___x_2133_, 0, v___x_2124_);
                    v___x_2136_ = v___x_2133_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2124_);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_2113_);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_2114_);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 3, v___y_2127_);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 4, v___x_2131_);
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
                lean_dec(v___y_2147_);
                lean_dec(v___x_2145_);
                if v_isShared_2094_ == 0 {
                    lean_ctor_set(v___x_2093_, 4, v_l_2115_);
                    lean_ctor_set(v___x_2093_, 3, v_l_1942_);
                    lean_ctor_set(v___x_2093_, 2, v_v_1941_);
                    lean_ctor_set(v___x_2093_, 1, v_k_1940_);
                    lean_ctor_set(v___x_2093_, 0, v___x_2148_);
                    v___x_2150_ = v___x_2093_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_1940_);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_1941_);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_l_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_l_2115_);
                    v___x_2150_ = v_reuseFailAlloc_2154_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_2151_ = lean_nat_add(v___x_1949_, v_size_2099_);
                if lean_obj_tag(v_r_2116_) == 0 {
                    v_size_2152_ = lean_ctor_get(v_r_2116_, 0);
                    lean_inc(v_size_2152_);
                    v___y_2126_ = v___x_2151_;
                    v___y_2127_ = v___x_2150_;
                    v___y_2128_ = v_size_2152_;
                    state = 55;
                    continue;
                } else {
                    v___x_2153_ = lean_unsigned_to_nat(0);
                    v___y_2126_ = v___x_2151_;
                    v___y_2127_ = v___x_2150_;
                    v___y_2128_ = v___x_2153_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_2110_ == 0 {
                    lean_ctor_set(v___x_2109_, 4, v___x_2168_);
                    lean_ctor_set(v___x_2109_, 0, v___x_2164_);
                    v___x_2170_ = v___x_2109_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_1940_);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_1941_);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_l_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2170_;
            }
            63 => {
                if lean_obj_tag(v_r_1943_) == 0 {
                    v_k_2182_ = lean_ctor_get(v___x_2095_, 0);
                    lean_inc(v_k_2182_);
                    v_v_2183_ = lean_ctor_get(v___x_2095_, 1);
                    lean_inc(v_v_2183_);
                    lean_dec_ref(v___x_2095_);
                    v_size_2184_ = lean_ctor_get(v_r_1943_, 0);
                    v___x_2185_ = lean_nat_add(v___x_1949_, v_size_1939_);
                    lean_dec(v_size_1939_);
                    v___x_2186_ = lean_nat_add(v___x_1949_, v_size_2184_);
                    if v_isShared_2094_ == 0 {
                        lean_ctor_set(v___x_2093_, 4, v_tree_2096_);
                        lean_ctor_set(v___x_2093_, 3, v_r_1943_);
                        lean_ctor_set(v___x_2093_, 2, v_v_2183_);
                        lean_ctor_set(v___x_2093_, 1, v_k_2182_);
                        lean_ctor_set(v___x_2093_, 0, v___x_2186_);
                        v___x_2188_ = v___x_2093_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2186_);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_2182_);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_2183_);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_r_1943_);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_tree_2096_);
                        v___x_2188_ = v_reuseFailAlloc_2192_;
                        state = 64;
                        continue;
                    }
                } else {
                    lean_dec(v_size_1939_);
                    v_k_2193_ = lean_ctor_get(v___x_2095_, 0);
                    lean_inc(v_k_2193_);
                    v_v_2194_ = lean_ctor_get(v___x_2095_, 1);
                    lean_inc(v_v_2194_);
                    lean_dec_ref(v___x_2095_);
                    v___x_2195_ = lean_unsigned_to_nat(3);
                    if v_isShared_2094_ == 0 {
                        lean_ctor_set(v___x_2093_, 4, v_r_1943_);
                        lean_ctor_set(v___x_2093_, 3, v_r_1943_);
                        lean_ctor_set(v___x_2093_, 2, v_v_2194_);
                        lean_ctor_set(v___x_2093_, 1, v_k_2193_);
                        lean_ctor_set(v___x_2093_, 0, v___x_1949_);
                        v___x_2197_ = v___x_2093_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_1949_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2193_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2194_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_1943_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_r_1943_);
                        v___x_2197_ = v_reuseFailAlloc_2201_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_2181_ == 0 {
                    lean_ctor_set(v___x_2180_, 4, v___x_2188_);
                    lean_ctor_set(v___x_2180_, 0, v___x_2185_);
                    v___x_2190_ = v___x_2180_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2185_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_1940_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_1941_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_l_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 4, v___x_2188_);
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
                    lean_ctor_set(v___x_2180_, 4, v___x_2197_);
                    lean_ctor_set(v___x_2180_, 0, v___x_2195_);
                    v___x_2199_ = v___x_2180_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2195_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_1940_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_1941_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 4, v___x_2197_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2199_;
            }
            68 => {
                v_k_2211_ = lean_ctor_get(v___x_2095_, 0);
                lean_inc(v_k_2211_);
                v_v_2212_ = lean_ctor_get(v___x_2095_, 1);
                lean_inc(v_v_2212_);
                lean_dec_ref(v___x_2095_);
                v_k_2213_ = lean_ctor_get(v_r_1943_, 1);
                v_v_2214_ = lean_ctor_get(v_r_1943_, 2);
                v_isSharedCheck_2228_ = (!lean_is_exclusive(v_r_1943_)) as u8;
                if v_isSharedCheck_2228_ == 0 {
                    v_unused_2229_ = lean_ctor_get(v_r_1943_, 4);
                    lean_dec(v_unused_2229_);
                    v_unused_2230_ = lean_ctor_get(v_r_1943_, 3);
                    lean_dec(v_unused_2230_);
                    v_unused_2231_ = lean_ctor_get(v_r_1943_, 0);
                    lean_dec(v_unused_2231_);
                    v___x_2216_ = v_r_1943_;
                    v_isShared_2217_ = v_isSharedCheck_2228_;
                    state = 69;
                    continue;
                } else {
                    lean_inc(v_v_2214_);
                    lean_inc(v_k_2213_);
                    lean_dec(v_r_1943_);
                    v___x_2216_ = lean_box(0);
                    v_isShared_2217_ = v_isSharedCheck_2228_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_2218_ = lean_unsigned_to_nat(3);
                if v_isShared_2217_ == 0 {
                    lean_ctor_set(v___x_2216_, 4, v_l_1942_);
                    lean_ctor_set(v___x_2216_, 3, v_l_1942_);
                    lean_ctor_set(v___x_2216_, 2, v_v_1941_);
                    lean_ctor_set(v___x_2216_, 1, v_k_1940_);
                    lean_ctor_set(v___x_2216_, 0, v___x_1949_);
                    v___x_2220_ = v___x_2216_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_1940_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_1941_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_l_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_l_1942_);
                    v___x_2220_ = v_reuseFailAlloc_2227_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2094_ == 0 {
                    lean_ctor_set(v___x_2093_, 4, v_l_1942_);
                    lean_ctor_set(v___x_2093_, 3, v_l_1942_);
                    lean_ctor_set(v___x_2093_, 2, v_v_2212_);
                    lean_ctor_set(v___x_2093_, 1, v_k_2211_);
                    lean_ctor_set(v___x_2093_, 0, v___x_1949_);
                    v___x_2222_ = v___x_2093_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2211_);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2212_);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_l_1942_);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_l_1942_);
                    v___x_2222_ = v_reuseFailAlloc_2226_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_2210_ == 0 {
                    lean_ctor_set(v___x_2209_, 4, v___x_2222_);
                    lean_ctor_set(v___x_2209_, 3, v___x_2220_);
                    lean_ctor_set(v___x_2209_, 2, v_v_2214_);
                    lean_ctor_set(v___x_2209_, 1, v_k_2213_);
                    lean_ctor_set(v___x_2209_, 0, v___x_2218_);
                    v___x_2224_ = v___x_2209_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2218_);
                    lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_k_2213_);
                    lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_v_2214_);
                    lean_ctor_set(v_reuseFailAlloc_2225_, 3, v___x_2220_);
                    lean_ctor_set(v_reuseFailAlloc_2225_, 4, v___x_2222_);
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
                v_size_2269_ = lean_ctor_get(v_l_2256_, 0);
                v_size_2270_ = lean_ctor_get(v_r_2257_, 0);
                v_k_2271_ = lean_ctor_get(v_r_2257_, 1);
                v_v_2272_ = lean_ctor_get(v_r_2257_, 2);
                v_l_2273_ = lean_ctor_get(v_r_2257_, 3);
                v_r_2274_ = lean_ctor_get(v_r_2257_, 4);
                v___x_2275_ = lean_unsigned_to_nat(2);
                v___x_2276_ = lean_nat_mul(v___x_2275_, v_size_2269_);
                v___x_2277_ = lean_nat_dec_lt(v_size_2270_, v___x_2276_);
                lean_dec(v___x_2276_);
                if v___x_2277_ == 0 {
                    lean_inc(v_r_2274_);
                    lean_inc(v_l_2273_);
                    lean_inc(v_v_2272_);
                    lean_inc(v_k_2271_);
                    v_isSharedCheck_2306_ = (!lean_is_exclusive(v_r_2257_)) as u8;
                    if v_isSharedCheck_2306_ == 0 {
                        v_unused_2307_ = lean_ctor_get(v_r_2257_, 4);
                        lean_dec(v_unused_2307_);
                        v_unused_2308_ = lean_ctor_get(v_r_2257_, 3);
                        lean_dec(v_unused_2308_);
                        v_unused_2309_ = lean_ctor_get(v_r_2257_, 2);
                        lean_dec(v_unused_2309_);
                        v_unused_2310_ = lean_ctor_get(v_r_2257_, 1);
                        lean_dec(v_unused_2310_);
                        v_unused_2311_ = lean_ctor_get(v_r_2257_, 0);
                        lean_dec(v_unused_2311_);
                        v___x_2279_ = v_r_2257_;
                        v_isShared_2280_ = v_isSharedCheck_2306_;
                        state = 76;
                        continue;
                    } else {
                        lean_dec(v_r_2257_);
                        v___x_2279_ = lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2306_;
                        state = 76;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1762_);
                    v___x_2312_ = lean_nat_add(v___x_2251_, v_size_2253_);
                    lean_dec(v_size_2253_);
                    v___x_2313_ = lean_nat_add(v___x_2312_, v_size_2252_);
                    lean_dec(v___x_2312_);
                    v___x_2314_ = lean_nat_add(v___x_2251_, v_size_2252_);
                    lean_dec(v_size_2252_);
                    v___x_2315_ = lean_nat_add(v___x_2314_, v_size_2270_);
                    lean_dec(v___x_2314_);
                    lean_inc_ref(v_impl_2250_);
                    if v_isShared_2268_ == 0 {
                        lean_ctor_set(v___x_2267_, 4, v_impl_2250_);
                        lean_ctor_set(v___x_2267_, 3, v_r_2257_);
                        lean_ctor_set(v___x_2267_, 2, v_v_1758_);
                        lean_ctor_set(v___x_2267_, 1, v_k_1757_);
                        lean_ctor_set(v___x_2267_, 0, v___x_2315_);
                        v___x_2317_ = v___x_2267_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2315_);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_1757_);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_1758_);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_r_2257_);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_impl_2250_);
                        v___x_2317_ = v_reuseFailAlloc_2330_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_2281_ = lean_nat_add(v___x_2251_, v_size_2253_);
                lean_dec(v_size_2253_);
                v___x_2282_ = lean_nat_add(v___x_2281_, v_size_2252_);
                lean_dec(v___x_2281_);
                v___x_2294_ = lean_nat_add(v___x_2251_, v_size_2269_);
                if lean_obj_tag(v_l_2273_) == 0 {
                    v_size_2304_ = lean_ctor_get(v_l_2273_, 0);
                    lean_inc(v_size_2304_);
                    v___y_2296_ = v_size_2304_;
                    state = 80;
                    continue;
                } else {
                    v___x_2305_ = lean_unsigned_to_nat(0);
                    v___y_2296_ = v___x_2305_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_2287_ = lean_nat_add(v___y_2284_, v___y_2286_);
                lean_dec(v___y_2286_);
                lean_dec(v___y_2284_);
                if v_isShared_2280_ == 0 {
                    lean_ctor_set(v___x_2279_, 4, v_impl_2250_);
                    lean_ctor_set(v___x_2279_, 3, v_r_2274_);
                    lean_ctor_set(v___x_2279_, 2, v_v_1758_);
                    lean_ctor_set(v___x_2279_, 1, v_k_1757_);
                    lean_ctor_set(v___x_2279_, 0, v___x_2287_);
                    v___x_2289_ = v___x_2279_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2287_);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_r_2274_);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_impl_2250_);
                    v___x_2289_ = v_reuseFailAlloc_2293_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_2268_ == 0 {
                    lean_ctor_set(v___x_2267_, 4, v___x_2289_);
                    lean_ctor_set(v___x_2267_, 3, v___y_2285_);
                    lean_ctor_set(v___x_2267_, 2, v_v_2272_);
                    lean_ctor_set(v___x_2267_, 1, v_k_2271_);
                    lean_ctor_set(v___x_2267_, 0, v___x_2282_);
                    v___x_2291_ = v___x_2267_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2282_);
                    lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2271_);
                    lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2272_);
                    lean_ctor_set(v_reuseFailAlloc_2292_, 3, v___y_2285_);
                    lean_ctor_set(v_reuseFailAlloc_2292_, 4, v___x_2289_);
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
                lean_dec(v___y_2296_);
                lean_dec(v___x_2294_);
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v_l_2273_);
                    lean_ctor_set(v___x_1762_, 3, v_l_2256_);
                    lean_ctor_set(v___x_1762_, 2, v_v_2255_);
                    lean_ctor_set(v___x_1762_, 1, v_k_2254_);
                    lean_ctor_set(v___x_1762_, 0, v___x_2297_);
                    v___x_2299_ = v___x_1762_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2297_);
                    lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_k_2254_);
                    lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_v_2255_);
                    lean_ctor_set(v_reuseFailAlloc_2303_, 3, v_l_2256_);
                    lean_ctor_set(v_reuseFailAlloc_2303_, 4, v_l_2273_);
                    v___x_2299_ = v_reuseFailAlloc_2303_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_2300_ = lean_nat_add(v___x_2251_, v_size_2252_);
                lean_dec(v_size_2252_);
                if lean_obj_tag(v_r_2274_) == 0 {
                    v_size_2301_ = lean_ctor_get(v_r_2274_, 0);
                    lean_inc(v_size_2301_);
                    v___y_2284_ = v___x_2300_;
                    v___y_2285_ = v___x_2299_;
                    v___y_2286_ = v_size_2301_;
                    state = 77;
                    continue;
                } else {
                    v___x_2302_ = lean_unsigned_to_nat(0);
                    v___y_2284_ = v___x_2300_;
                    v___y_2285_ = v___x_2299_;
                    v___y_2286_ = v___x_2302_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_2324_ = (!lean_is_exclusive(v_impl_2250_)) as u8;
                if v_isSharedCheck_2324_ == 0 {
                    v_unused_2325_ = lean_ctor_get(v_impl_2250_, 4);
                    lean_dec(v_unused_2325_);
                    v_unused_2326_ = lean_ctor_get(v_impl_2250_, 3);
                    lean_dec(v_unused_2326_);
                    v_unused_2327_ = lean_ctor_get(v_impl_2250_, 2);
                    lean_dec(v_unused_2327_);
                    v_unused_2328_ = lean_ctor_get(v_impl_2250_, 1);
                    lean_dec(v_unused_2328_);
                    v_unused_2329_ = lean_ctor_get(v_impl_2250_, 0);
                    lean_dec(v_unused_2329_);
                    v___x_2319_ = v_impl_2250_;
                    v_isShared_2320_ = v_isSharedCheck_2324_;
                    state = 83;
                    continue;
                } else {
                    lean_dec(v_impl_2250_);
                    v___x_2319_ = lean_box(0);
                    v_isShared_2320_ = v_isSharedCheck_2324_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_2320_ == 0 {
                    lean_ctor_set(v___x_2319_, 4, v___x_2317_);
                    lean_ctor_set(v___x_2319_, 3, v_l_2256_);
                    lean_ctor_set(v___x_2319_, 2, v_v_2255_);
                    lean_ctor_set(v___x_2319_, 1, v_k_2254_);
                    lean_ctor_set(v___x_2319_, 0, v___x_2313_);
                    v___x_2322_ = v___x_2319_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2313_);
                    lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_k_2254_);
                    lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_v_2255_);
                    lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_l_2256_);
                    lean_ctor_set(v_reuseFailAlloc_2323_, 4, v___x_2317_);
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
                v_size_2350_ = lean_ctor_get(v_r_2343_, 0);
                v___x_2351_ = lean_nat_add(v___x_2251_, v_size_2344_);
                lean_dec(v_size_2344_);
                v___x_2352_ = lean_nat_add(v___x_2251_, v_size_2350_);
                if v_isShared_2349_ == 0 {
                    lean_ctor_set(v___x_2348_, 4, v_impl_2250_);
                    lean_ctor_set(v___x_2348_, 3, v_r_2343_);
                    lean_ctor_set(v___x_2348_, 2, v_v_1758_);
                    lean_ctor_set(v___x_2348_, 1, v_k_1757_);
                    lean_ctor_set(v___x_2348_, 0, v___x_2352_);
                    v___x_2354_ = v___x_2348_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_r_2343_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_impl_2250_);
                    v___x_2354_ = v_reuseFailAlloc_2358_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v___x_2354_);
                    lean_ctor_set(v___x_1762_, 3, v_l_2342_);
                    lean_ctor_set(v___x_1762_, 2, v_v_2346_);
                    lean_ctor_set(v___x_1762_, 1, v_k_2345_);
                    lean_ctor_set(v___x_1762_, 0, v___x_2351_);
                    v___x_2356_ = v___x_1762_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2345_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2346_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_l_2342_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 4, v___x_2354_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_2356_;
            }
            89 => {
                v___x_2367_ = lean_unsigned_to_nat(3);
                if v_isShared_2366_ == 0 {
                    lean_ctor_set(v___x_2365_, 3, v_r_2343_);
                    lean_ctor_set(v___x_2365_, 2, v_v_1758_);
                    lean_ctor_set(v___x_2365_, 1, v_k_1757_);
                    lean_ctor_set(v___x_2365_, 0, v___x_2251_);
                    v___x_2369_ = v___x_2365_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2251_);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_r_2343_);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_r_2343_);
                    v___x_2369_ = v_reuseFailAlloc_2373_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v___x_2369_);
                    lean_ctor_set(v___x_1762_, 3, v_l_2342_);
                    lean_ctor_set(v___x_1762_, 2, v_v_2363_);
                    lean_ctor_set(v___x_1762_, 1, v_k_2362_);
                    lean_ctor_set(v___x_1762_, 0, v___x_2367_);
                    v___x_2371_ = v___x_1762_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2367_);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_k_2362_);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_v_2363_);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_l_2342_);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 4, v___x_2369_);
                    v___x_2371_ = v_reuseFailAlloc_2372_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_2371_;
            }
            92 => {
                v_k_2384_ = lean_ctor_get(v_r_2378_, 1);
                v_v_2385_ = lean_ctor_get(v_r_2378_, 2);
                v_isSharedCheck_2399_ = (!lean_is_exclusive(v_r_2378_)) as u8;
                if v_isSharedCheck_2399_ == 0 {
                    v_unused_2400_ = lean_ctor_get(v_r_2378_, 4);
                    lean_dec(v_unused_2400_);
                    v_unused_2401_ = lean_ctor_get(v_r_2378_, 3);
                    lean_dec(v_unused_2401_);
                    v_unused_2402_ = lean_ctor_get(v_r_2378_, 0);
                    lean_dec(v_unused_2402_);
                    v___x_2387_ = v_r_2378_;
                    v_isShared_2388_ = v_isSharedCheck_2399_;
                    state = 93;
                    continue;
                } else {
                    lean_inc(v_v_2385_);
                    lean_inc(v_k_2384_);
                    lean_dec(v_r_2378_);
                    v___x_2387_ = lean_box(0);
                    v_isShared_2388_ = v_isSharedCheck_2399_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_2389_ = lean_unsigned_to_nat(3);
                if v_isShared_2388_ == 0 {
                    lean_ctor_set(v___x_2387_, 4, v_l_2342_);
                    lean_ctor_set(v___x_2387_, 3, v_l_2342_);
                    lean_ctor_set(v___x_2387_, 2, v_v_2380_);
                    lean_ctor_set(v___x_2387_, 1, v_k_2379_);
                    lean_ctor_set(v___x_2387_, 0, v___x_2251_);
                    v___x_2391_ = v___x_2387_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2251_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2379_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2380_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_l_2342_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_l_2342_);
                    v___x_2391_ = v_reuseFailAlloc_2398_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_2383_ == 0 {
                    lean_ctor_set(v___x_2382_, 4, v_l_2342_);
                    lean_ctor_set(v___x_2382_, 2, v_v_1758_);
                    lean_ctor_set(v___x_2382_, 1, v_k_1757_);
                    lean_ctor_set(v___x_2382_, 0, v___x_2251_);
                    v___x_2393_ = v___x_2382_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2251_);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_1757_);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_1758_);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_l_2342_);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_l_2342_);
                    v___x_2393_ = v_reuseFailAlloc_2397_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 4, v___x_2393_);
                    lean_ctor_set(v___x_1762_, 3, v___x_2391_);
                    lean_ctor_set(v___x_1762_, 2, v_v_2385_);
                    lean_ctor_set(v___x_1762_, 1, v_k_2384_);
                    lean_ctor_set(v___x_1762_, 0, v___x_2389_);
                    v___x_2395_ = v___x_1762_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2389_);
                    lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_k_2384_);
                    lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_v_2385_);
                    lean_ctor_set(v_reuseFailAlloc_2396_, 3, v___x_2391_);
                    lean_ctor_set(v_reuseFailAlloc_2396_, 4, v___x_2393_);
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
    mut v_k_2416_: *mut LeanObject,
    mut v_t_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_k_2416_, v_t_2417_);
    lean_dec(v_k_2416_);
    return v_res_2418_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(
    mut v_name_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2422_ = lean_st_ref_get(v_a_2420_);
                v_remaining_2423_ = lean_ctor_get(v___x_2422_, 1);
                lean_inc(v_remaining_2423_);
                lean_dec(v___x_2422_);
                v___x_2424_ = l_Lean_NameSet_contains(v_remaining_2423_, v_name_2419_);
                lean_dec(v_remaining_2423_);
                if v___x_2424_ == 0 {
                    lean_dec(v_name_2419_);
                    v___x_2425_ = lean_box((v___x_2424_) as usize);
                    v___x_2426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2426_, 0, v___x_2425_);
                    return v___x_2426_;
                } else {
                    v___x_2427_ = lean_st_ref_take(v_a_2420_);
                    v_env_2428_ = lean_ctor_get(v___x_2427_, 0);
                    v_remaining_2429_ = lean_ctor_get(v___x_2427_, 1);
                    v_pending_2430_ = lean_ctor_get(v___x_2427_, 2);
                    v_postponedConstructors_2431_ = lean_ctor_get(v___x_2427_, 3);
                    v_postponedRecursors_2432_ = lean_ctor_get(v___x_2427_, 4);
                    v_isSharedCheck_2444_ = (!lean_is_exclusive(v___x_2427_)) as u8;
                    if v_isSharedCheck_2444_ == 0 {
                        v___x_2434_ = v___x_2427_;
                        v_isShared_2435_ = v_isSharedCheck_2444_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_postponedRecursors_2432_);
                        lean_inc(v_postponedConstructors_2431_);
                        lean_inc(v_pending_2430_);
                        lean_inc(v_remaining_2429_);
                        lean_inc(v_env_2428_);
                        lean_dec(v___x_2427_);
                        v___x_2434_ = lean_box(0);
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
                    lean_ctor_set(v___x_2434_, 2, v___x_2437_);
                    lean_ctor_set(v___x_2434_, 1, v___x_2436_);
                    v___x_2439_ = v___x_2434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_env_2428_);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2436_);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 2, v___x_2437_);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 3, v_postponedConstructors_2431_);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 4, v_postponedRecursors_2432_);
                    v___x_2439_ = v_reuseFailAlloc_2443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2440_ = lean_st_ref_set(v_a_2420_, v___x_2439_);
                v___x_2441_ = lean_box((v___x_2424_) as usize);
                v___x_2442_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2442_, 0, v___x_2441_);
                return v___x_2442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg___boxed(
    mut v_name_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2448_: *mut LeanObject = core::ptr::null_mut();
    v_res_2448_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(v_name_2445_, v_a_2446_);
    lean_dec(v_a_2446_);
    return v_res_2448_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo(
    mut v_name_2449_: *mut LeanObject,
    mut v_a_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    v___x_2453_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(v_name_2449_, v_a_2451_);
    return v___x_2453_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___boxed(
    mut v_name_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2458_: *mut LeanObject = core::ptr::null_mut();
    v_res_2458_ = l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo(
        v_name_2454_,
        v_a_2455_,
        v_a_2456_,
    );
    lean_dec(v_a_2456_);
    lean_dec_ref(v_a_2455_);
    return v_res_2458_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0(
    mut v_00_u03b2_2459_: *mut LeanObject,
    mut v_k_2460_: *mut LeanObject,
    mut v_t_2461_: *mut LeanObject,
    mut v_h_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_k_2460_, v_t_2461_);
    return v___x_2463_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___boxed(
    mut v_00_u03b2_2464_: *mut LeanObject,
    mut v_k_2465_: *mut LeanObject,
    mut v_t_2466_: *mut LeanObject,
    mut v_h_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2468_: *mut LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0(v_00_u03b2_2464_, v_k_2465_, v_t_2466_, v_h_2467_);
    lean_dec(v_k_2465_);
    return v_res_2468_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(
    mut v_ex_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2471_ = l_Lean_Options_empty;
    v___x_2472_ = l_Lean_Kernel_Exception_toMessageData(v_ex_2469_, v___x_2471_);
    v___x_2473_ = l_Lean_MessageData_toString(v___x_2472_);
    v___x_2474_ = lean_alloc_ctor(18, 1, (0) as u32);
    lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    v___x_2475_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2475_, 0, v___x_2474_);
    return v___x_2475_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg___boxed(
    mut v_ex_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2478_: *mut LeanObject = core::ptr::null_mut();
    v_res_2478_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(
        v_ex_2476_,
    );
    return v_res_2478_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException(
    mut v_ex_2479_: *mut LeanObject,
    mut v_a_2480_: *mut LeanObject,
    mut v_a_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2483_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(
        v_ex_2479_,
    );
    return v___x_2483_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___boxed(
    mut v_ex_2484_: *mut LeanObject,
    mut v_a_2485_: *mut LeanObject,
    mut v_a_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2488_: *mut LeanObject = core::ptr::null_mut();
    v_res_2488_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException(
        v_ex_2484_, v_a_2485_, v_a_2486_,
    );
    lean_dec(v_a_2486_);
    lean_dec_ref(v_a_2485_);
    return v_res_2488_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
    mut v_d_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: usize = 0;
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v_unused_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2492_ = lean_st_ref_get(v_a_2490_);
                v_env_2493_ = lean_ctor_get(v___x_2492_, 0);
                lean_inc_ref(v_env_2493_);
                lean_dec(v___x_2492_);
                v___x_2494_ = 0usize;
                v___x_2495_ = lean_box(0);
                v___x_2496_ = lean_add_decl(v_env_2493_, v___x_2494_, v_d_2489_, v___x_2495_);
                if lean_obj_tag(v___x_2496_) == 0 {
                    v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
                    lean_inc(v_a_2497_);
                    lean_dec_ref_known(v___x_2496_, 1);
                    v___x_2498_ = l___private_Lean_Replay_0__Lean_Environment_Replay_throwKernelException___redArg(v_a_2497_);
                    return v___x_2498_;
                } else {
                    v_a_2499_ = lean_ctor_get(v___x_2496_, 0);
                    v_isSharedCheck_2521_ = (!lean_is_exclusive(v___x_2496_)) as u8;
                    if v_isSharedCheck_2521_ == 0 {
                        v___x_2501_ = v___x_2496_;
                        v_isShared_2502_ = v_isSharedCheck_2521_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2499_);
                        lean_dec(v___x_2496_);
                        v___x_2501_ = lean_box(0);
                        v_isShared_2502_ = v_isSharedCheck_2521_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2503_ = lean_st_ref_take(v_a_2490_);
                v_remaining_2504_ = lean_ctor_get(v___x_2503_, 1);
                v_pending_2505_ = lean_ctor_get(v___x_2503_, 2);
                v_postponedConstructors_2506_ = lean_ctor_get(v___x_2503_, 3);
                v_postponedRecursors_2507_ = lean_ctor_get(v___x_2503_, 4);
                v_isSharedCheck_2519_ = (!lean_is_exclusive(v___x_2503_)) as u8;
                if v_isSharedCheck_2519_ == 0 {
                    v_unused_2520_ = lean_ctor_get(v___x_2503_, 0);
                    lean_dec(v_unused_2520_);
                    v___x_2509_ = v___x_2503_;
                    v_isShared_2510_ = v_isSharedCheck_2519_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_postponedRecursors_2507_);
                    lean_inc(v_postponedConstructors_2506_);
                    lean_inc(v_pending_2505_);
                    lean_inc(v_remaining_2504_);
                    lean_dec(v___x_2503_);
                    v___x_2509_ = lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2510_ == 0 {
                    lean_ctor_set(v___x_2509_, 0, v_a_2499_);
                    v___x_2512_ = v___x_2509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2499_);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_remaining_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_pending_2505_);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_postponedConstructors_2506_);
                    lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_postponedRecursors_2507_);
                    v___x_2512_ = v_reuseFailAlloc_2518_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2513_ = lean_st_ref_set(v_a_2490_, v___x_2512_);
                v___x_2514_ = lean_box(0);
                if v_isShared_2502_ == 0 {
                    lean_ctor_set_tag(v___x_2501_, 0);
                    lean_ctor_set(v___x_2501_, 0, v___x_2514_);
                    v___x_2516_ = v___x_2501_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
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
    mut v_d_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2525_: *mut LeanObject = core::ptr::null_mut();
    v_res_2525_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v_d_2522_, v_a_2523_);
    lean_dec(v_a_2523_);
    lean_dec(v_d_2522_);
    return v_res_2525_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl(
    mut v_d_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v_d_2526_, v_a_2528_);
    return v___x_2530_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___boxed(
    mut v_d_2531_: *mut LeanObject,
    mut v_a_2532_: *mut LeanObject,
    mut v_a_2533_: *mut LeanObject,
    mut v_a_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2535_: *mut LeanObject = core::ptr::null_mut();
    v_res_2535_ =
        l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl(v_d_2531_, v_a_2532_, v_a_2533_);
    lean_dec(v_a_2533_);
    lean_dec_ref(v_a_2532_);
    lean_dec(v_d_2531_);
    return v_res_2535_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0()
-> *mut LeanObject {
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    v___x_2536_ = l_instMonadEIO(lean_box(0));
    return v___x_2536_;
}
pub unsafe fn l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10(
    mut v_msg_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_32059__overap_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    v___x_2541_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0_once), _init_l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___closed__0);
    v___x_2542_ = l_StateRefT_x27_instMonad___redArg(v___x_2541_);
    v___x_2543_ = lean_box(0);
    v___x_2544_ = l_instInhabitedOfMonad___redArg(v___x_2542_, v___x_2543_);
    v___f_2545_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2545_, 0, v___x_2544_);
    v___x_32059__overap_2546_ = lean_panic_fn_borrowed(v___f_2545_, v_msg_2537_);
    lean_dec_ref(v___f_2545_);
    lean_inc(v___y_2539_);
    lean_inc_ref(v___y_2538_);
    v___x_2547_ = lean_apply_3(
        v___x_32059__overap_2546_,
        v___y_2538_,
        v___y_2539_,
        lean_box(0),
    );
    return v___x_2547_;
}
pub unsafe fn l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10___boxed(
    mut v_msg_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
    mut v___y_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2552_: *mut LeanObject = core::ptr::null_mut();
    v_res_2552_ =
        l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10(
            v_msg_2548_,
            v___y_2549_,
            v___y_2550_,
        );
    lean_dec(v___y_2550_);
    lean_dec_ref(v___y_2549_);
    return v_res_2552_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
    mut v_name_2555_: *mut LeanObject,
    mut v_____r_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
    mut v___y_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2568_: u8 = 0;
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2560_ = lean_st_ref_take(v___y_2558_);
                v_env_2561_ = lean_ctor_get(v___x_2560_, 0);
                v_remaining_2562_ = lean_ctor_get(v___x_2560_, 1);
                v_pending_2563_ = lean_ctor_get(v___x_2560_, 2);
                v_postponedConstructors_2564_ = lean_ctor_get(v___x_2560_, 3);
                v_postponedRecursors_2565_ = lean_ctor_get(v___x_2560_, 4);
                v_isSharedCheck_2576_ = (!lean_is_exclusive(v___x_2560_)) as u8;
                if v_isSharedCheck_2576_ == 0 {
                    v___x_2567_ = v___x_2560_;
                    v_isShared_2568_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_postponedRecursors_2565_);
                    lean_inc(v_postponedConstructors_2564_);
                    lean_inc(v_pending_2563_);
                    lean_inc(v_remaining_2562_);
                    lean_inc(v_env_2561_);
                    lean_dec(v___x_2560_);
                    v___x_2567_ = lean_box(0);
                    v_isShared_2568_ = v_isSharedCheck_2576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2569_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Environment_Replay_isTodo_spec__0___redArg(v_name_2555_, v_pending_2563_);
                if v_isShared_2568_ == 0 {
                    lean_ctor_set(v___x_2567_, 2, v___x_2569_);
                    v___x_2571_ = v___x_2567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_env_2561_);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_remaining_2562_);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 2, v___x_2569_);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_postponedConstructors_2564_);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_postponedRecursors_2565_);
                    v___x_2571_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2572_ = lean_st_ref_set(v___y_2558_, v___x_2571_);
                v___x_2573_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___closed__0;
                v___x_2574_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2574_, 0, v___x_2573_);
                return v___x_2574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___boxed(
    mut v_name_2577_: *mut LeanObject,
    mut v_____r_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
    mut v___y_2581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2582_: *mut LeanObject = core::ptr::null_mut();
    v_res_2582_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(
        v_name_2577_,
        v_____r_2578_,
        v___y_2579_,
        v___y_2580_,
    );
    lean_dec(v___y_2580_);
    lean_dec_ref(v___y_2579_);
    lean_dec(v_name_2577_);
    return v_res_2582_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1(
    mut v_val_2583_: *mut LeanObject,
    mut v___f_2584_: *mut LeanObject,
    mut v_____r_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
    mut v___y_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2589_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_2589_, 0, v_val_2583_);
                v___x_2590_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(
                    v___x_2589_,
                    v___y_2587_,
                );
                lean_dec_ref_known(v___x_2589_, 1);
                if lean_obj_tag(v___x_2590_) == 0 {
                    v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
                    lean_inc(v_a_2591_);
                    lean_dec_ref_known(v___x_2590_, 1);
                    lean_inc(v___y_2587_);
                    lean_inc_ref(v___y_2586_);
                    v___x_2592_ = lean_apply_4(
                        v___f_2584_,
                        v_a_2591_,
                        v___y_2586_,
                        v___y_2587_,
                        lean_box(0),
                    );
                    return v___x_2592_;
                } else {
                    lean_dec_ref(v___f_2584_);
                    v_a_2593_ = lean_ctor_get(v___x_2590_, 0);
                    v_isSharedCheck_2600_ = (!lean_is_exclusive(v___x_2590_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2595_ = v___x_2590_;
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2593_);
                        lean_dec(v___x_2590_);
                        v___x_2595_ = lean_box(0);
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
                    v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
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
    mut v_val_2601_: *mut LeanObject,
    mut v___f_2602_: *mut LeanObject,
    mut v_____r_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2607_: *mut LeanObject = core::ptr::null_mut();
    v_res_2607_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1(
        v_val_2601_,
        v___f_2602_,
        v_____r_2603_,
        v___y_2604_,
        v___y_2605_,
    );
    lean_dec(v___y_2605_);
    lean_dec_ref(v___y_2604_);
    return v_res_2607_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(
    mut v___f_2608_: *mut LeanObject,
    mut v_x_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    v___x_2613_ = lean_box(0);
    lean_inc(v___y_2611_);
    lean_inc_ref(v___y_2610_);
    v___x_2614_ = lean_apply_4(
        v___f_2608_,
        v___x_2613_,
        v___y_2610_,
        v___y_2611_,
        lean_box(0),
    );
    return v___x_2614_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2___boxed(
    mut v___f_2615_: *mut LeanObject,
    mut v_x_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2620_: *mut LeanObject = core::ptr::null_mut();
    v_res_2620_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(
        v___f_2615_,
        v_x_2616_,
        v___y_2617_,
        v___y_2618_,
    );
    lean_dec(v___y_2618_);
    lean_dec_ref(v___y_2617_);
    lean_dec(v_x_2616_);
    return v_res_2620_;
}
pub unsafe fn l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(
    mut v_x_2621_: *mut LeanObject,
    mut v_x_2622_: *mut LeanObject,
) -> u8 {
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: u8 = 0;
    let mut v_head_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2621_) == 0 {
                    if lean_obj_tag(v_x_2622_) == 0 {
                        v___x_2623_ = 1;
                        return v___x_2623_;
                    } else {
                        v___x_2624_ = 0;
                        return v___x_2624_;
                    }
                } else {
                    if lean_obj_tag(v_x_2622_) == 0 {
                        v___x_2625_ = 0;
                        return v___x_2625_;
                    } else {
                        v_head_2626_ = lean_ctor_get(v_x_2621_, 0);
                        v_tail_2627_ = lean_ctor_get(v_x_2621_, 1);
                        v_head_2628_ = lean_ctor_get(v_x_2622_, 0);
                        v_tail_2629_ = lean_ctor_get(v_x_2622_, 1);
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
    mut v_x_2632_: *mut LeanObject,
    mut v_x_2633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2634_: u8 = 0;
    let mut v_r_2635_: *mut LeanObject = core::ptr::null_mut();
    v_res_2634_ =
        l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(
            v_x_2632_, v_x_2633_,
        );
    lean_dec(v_x_2633_);
    lean_dec(v_x_2632_);
    v_r_2635_ = lean_box((v_res_2634_) as usize);
    return v_r_2635_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(
    mut v_msg_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    v___x_2637_ = l_Lean_instInhabitedConstantInfo_default;
    v___x_2638_ = lean_panic_fn_borrowed(v___x_2637_, v_msg_2636_);
    return v___x_2638_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__2;
    v___x_2643_ = lean_unsigned_to_nat(11);
    v___x_2644_ = lean_unsigned_to_nat(163);
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
    mut v_a_2648_: *mut LeanObject,
    mut v_x_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2649_) == 0 {
                    v___x_2650_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___closed__3);
                    v___x_2651_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(v___x_2650_);
                    return v___x_2651_;
                } else {
                    v_key_2652_ = lean_ctor_get(v_x_2649_, 0);
                    v_value_2653_ = lean_ctor_get(v_x_2649_, 1);
                    v_tail_2654_ = lean_ctor_get(v_x_2649_, 2);
                    v___x_2655_ = lean_name_eq(v_key_2652_, v_a_2648_);
                    if v___x_2655_ == 0 {
                        v_x_2649_ = v_tail_2654_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2653_);
                        return v_value_2653_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0___boxed(
    mut v_a_2657_: *mut LeanObject,
    mut v_x_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2659_: *mut LeanObject = core::ptr::null_mut();
    v_res_2659_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0_spec__0(v_a_2657_, v_x_2658_);
    lean_dec(v_x_2658_);
    lean_dec(v_a_2657_);
    return v_res_2659_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0()
-> u64 {
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: u64 = 0;
    v___x_2660_ = lean_unsigned_to_nat(1723);
    v___x_2661_ = lean_uint64_of_nat(v___x_2660_);
    return v___x_2661_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0(
    mut v_m_2662_: *mut LeanObject,
    mut v_a_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u64 = 0;
    let mut v_hash_2682_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2664_ = lean_ctor_get(v_m_2662_, 1);
                v___x_2665_ = lean_array_get_size(v_buckets_2664_);
                if lean_obj_tag(v_a_2663_) == 0 {
                    v___x_2681_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0);
                    v___y_2667_ = v___x_2681_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2682_ = lean_ctor_get_uint64(
                        v_a_2663_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2685_: *mut LeanObject = core::ptr::null_mut();
    v_res_2685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0(v_m_2683_, v_a_2684_);
    lean_dec(v_a_2684_);
    lean_dec_ref(v_m_2683_);
    return v_res_2685_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(
    mut v_x_2686_: *mut LeanObject,
    mut v_x_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2686_) == 0 {
                    v___x_2690_ = l_List_reverse___redArg(v_x_2687_);
                    v___x_2691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                    return v___x_2691_;
                } else {
                    v_head_2692_ = lean_ctor_get(v_x_2686_, 0);
                    v_tail_2693_ = lean_ctor_get(v_x_2686_, 1);
                    v_isSharedCheck_2702_ = (!lean_is_exclusive(v_x_2686_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2695_ = v_x_2686_;
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2693_);
                        lean_inc(v_head_2692_);
                        lean_dec(v_x_2686_);
                        v___x_2695_ = lean_box(0);
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0(v___y_2688_, v_head_2692_);
                lean_dec(v_head_2692_);
                if v_isShared_2696_ == 0 {
                    lean_ctor_set(v___x_2695_, 1, v_x_2687_);
                    lean_ctor_set(v___x_2695_, 0, v___x_2697_);
                    v___x_2699_ = v___x_2695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_x_2687_);
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
    mut v_x_2703_: *mut LeanObject,
    mut v_x_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2707_: *mut LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_x_2703_, v_x_2704_, v___y_2705_);
    lean_dec_ref(v___y_2705_);
    return v_res_2707_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7(
    mut v_x_2708_: *mut LeanObject,
    mut v_x_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
    mut v___y_2711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2708_) == 0 {
                    v___x_2713_ = l_List_reverse___redArg(v_x_2709_);
                    v___x_2714_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2714_, 0, v___x_2713_);
                    return v___x_2714_;
                } else {
                    v_head_2715_ = lean_ctor_get(v_x_2708_, 0);
                    v_tail_2716_ = lean_ctor_get(v_x_2708_, 1);
                    v_isSharedCheck_2730_ = (!lean_is_exclusive(v_x_2708_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2718_ = v_x_2708_;
                        v_isShared_2719_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2716_);
                        lean_inc(v_head_2715_);
                        lean_dec(v_x_2708_);
                        v___x_2718_ = lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2720_ = l_Lean_ConstantInfo_inductiveVal_x21(v_head_2715_);
                v_ctors_2721_ = lean_ctor_get(v___x_2720_, 4);
                lean_inc(v_ctors_2721_);
                lean_dec_ref(v___x_2720_);
                v___x_2722_ = lean_box(0);
                v___x_2723_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_ctors_2721_, v___x_2722_, v___y_2710_);
                v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
                lean_inc(v_a_2724_);
                lean_dec_ref(v___x_2723_);
                v___x_2725_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2725_, 0, v_head_2715_);
                lean_ctor_set(v___x_2725_, 1, v_a_2724_);
                if v_isShared_2719_ == 0 {
                    lean_ctor_set(v___x_2718_, 1, v_x_2709_);
                    lean_ctor_set(v___x_2718_, 0, v___x_2725_);
                    v___x_2727_ = v___x_2718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2725_);
                    lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_x_2709_);
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
    mut v_x_2731_: *mut LeanObject,
    mut v_x_2732_: *mut LeanObject,
    mut v___y_2733_: *mut LeanObject,
    mut v___y_2734_: *mut LeanObject,
    mut v___y_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2736_: *mut LeanObject = core::ptr::null_mut();
    v_res_2736_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7(v_x_2731_, v_x_2732_, v___y_2733_, v___y_2734_);
    lean_dec(v___y_2734_);
    lean_dec_ref(v___y_2733_);
    return v_res_2736_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(
    mut v_a_2737_: *mut LeanObject,
    mut v_x_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2738_) == 0 {
                    v___x_2739_ = lean_box(0);
                    return v___x_2739_;
                } else {
                    v_key_2740_ = lean_ctor_get(v_x_2738_, 0);
                    v_value_2741_ = lean_ctor_get(v_x_2738_, 1);
                    v_tail_2742_ = lean_ctor_get(v_x_2738_, 2);
                    v___x_2743_ = lean_name_eq(v_key_2740_, v_a_2737_);
                    if v___x_2743_ == 0 {
                        v_x_2738_ = v_tail_2742_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2741_);
                        v___x_2745_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2745_, 0, v_value_2741_);
                        return v___x_2745_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg___boxed(
    mut v_a_2746_: *mut LeanObject,
    mut v_x_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2748_: *mut LeanObject = core::ptr::null_mut();
    v_res_2748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_2746_, v_x_2747_);
    lean_dec(v_x_2747_);
    lean_dec(v_a_2746_);
    return v_res_2748_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(
    mut v_m_2749_: *mut LeanObject,
    mut v_a_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u64 = 0;
    let mut v_hash_2769_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2751_ = lean_ctor_get(v_m_2749_, 1);
                v___x_2752_ = lean_array_get_size(v_buckets_2751_);
                if lean_obj_tag(v_a_2750_) == 0 {
                    v___x_2768_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__0___closed__0);
                    v___y_2754_ = v___x_2768_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2769_ = lean_ctor_get_uint64(
                        v_a_2750_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_2770_: *mut LeanObject,
    mut v_a_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v_m_2770_, v_a_2771_);
    lean_dec(v_a_2771_);
    lean_dec_ref(v_m_2770_);
    return v_res_2772_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(
    mut v_as_x27_2773_: *mut LeanObject,
    mut v_b_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2773_) == 0 {
                    v___x_2777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2777_, 0, v_b_2774_);
                    return v___x_2777_;
                } else {
                    v_head_2778_ = lean_ctor_get(v_as_x27_2773_, 0);
                    v_tail_2779_ = lean_ctor_get(v_as_x27_2773_, 1);
                    v___x_2780_ = lean_st_ref_take(v___y_2775_);
                    v_env_2781_ = lean_ctor_get(v___x_2780_, 0);
                    v_remaining_2782_ = lean_ctor_get(v___x_2780_, 1);
                    v_pending_2783_ = lean_ctor_get(v___x_2780_, 2);
                    v_postponedConstructors_2784_ = lean_ctor_get(v___x_2780_, 3);
                    v_postponedRecursors_2785_ = lean_ctor_get(v___x_2780_, 4);
                    v_isSharedCheck_2798_ = (!lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2798_ == 0 {
                        v___x_2787_ = v___x_2780_;
                        v_isShared_2788_ = v_isSharedCheck_2798_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_postponedRecursors_2785_);
                        lean_inc(v_postponedConstructors_2784_);
                        lean_inc(v_pending_2783_);
                        lean_inc(v_remaining_2782_);
                        lean_inc(v_env_2781_);
                        lean_dec(v___x_2780_);
                        v___x_2787_ = lean_box(0);
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
                lean_dec(v___x_2789_);
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 2, v___x_2791_);
                    lean_ctor_set(v___x_2787_, 1, v___x_2790_);
                    v___x_2793_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_env_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 2, v___x_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_postponedConstructors_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 4, v_postponedRecursors_2785_);
                    v___x_2793_ = v_reuseFailAlloc_2797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2794_ = lean_st_ref_set(v___y_2775_, v___x_2793_);
                v___x_2795_ = lean_box(0);
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
    mut v_as_x27_2799_: *mut LeanObject,
    mut v_b_2800_: *mut LeanObject,
    mut v___y_2801_: *mut LeanObject,
    mut v___y_2802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2803_: *mut LeanObject = core::ptr::null_mut();
    v_res_2803_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_2799_, v_b_2800_, v___y_2801_);
    lean_dec(v___y_2801_);
    lean_dec(v_as_x27_2799_);
    return v_res_2803_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__1(
    mut v_a_2804_: *mut LeanObject,
    mut v_a_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2804_) == 0 {
                    v___x_2806_ = l_List_reverse___redArg(v_a_2805_);
                    return v___x_2806_;
                } else {
                    v_head_2807_ = lean_ctor_get(v_a_2804_, 0);
                    v_tail_2808_ = lean_ctor_get(v_a_2804_, 1);
                    v_isSharedCheck_2819_ = (!lean_is_exclusive(v_a_2804_)) as u8;
                    if v_isSharedCheck_2819_ == 0 {
                        v___x_2810_ = v_a_2804_;
                        v_isShared_2811_ = v_isSharedCheck_2819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2808_);
                        lean_inc(v_head_2807_);
                        lean_dec(v_a_2804_);
                        v___x_2810_ = lean_box(0);
                        v_isShared_2811_ = v_isSharedCheck_2819_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2812_ = l_Lean_ConstantInfo_name(v_head_2807_);
                v___x_2813_ = l_Lean_ConstantInfo_type(v_head_2807_);
                lean_dec(v_head_2807_);
                v___x_2814_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2814_, 0, v___x_2812_);
                lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                if v_isShared_2811_ == 0 {
                    lean_ctor_set(v___x_2810_, 1, v_a_2805_);
                    lean_ctor_set(v___x_2810_, 0, v___x_2814_);
                    v___x_2816_ = v___x_2810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2814_);
                    lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_a_2805_);
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
    mut v_a_2820_: *mut LeanObject,
    mut v_a_2821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v_fst_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2820_) == 0 {
                    v___x_2822_ = l_List_reverse___redArg(v_a_2821_);
                    return v___x_2822_;
                } else {
                    v_head_2823_ = lean_ctor_get(v_a_2820_, 0);
                    v_tail_2824_ = lean_ctor_get(v_a_2820_, 1);
                    v_isSharedCheck_2839_ = (!lean_is_exclusive(v_a_2820_)) as u8;
                    if v_isSharedCheck_2839_ == 0 {
                        v___x_2826_ = v_a_2820_;
                        v_isShared_2827_ = v_isSharedCheck_2839_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2824_);
                        lean_inc(v_head_2823_);
                        lean_dec(v_a_2820_);
                        v___x_2826_ = lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2839_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2828_ = lean_ctor_get(v_head_2823_, 0);
                lean_inc(v_fst_2828_);
                v_snd_2829_ = lean_ctor_get(v_head_2823_, 1);
                lean_inc(v_snd_2829_);
                lean_dec(v_head_2823_);
                v___x_2830_ = l_Lean_ConstantInfo_name(v_fst_2828_);
                v___x_2831_ = l_Lean_ConstantInfo_type(v_fst_2828_);
                lean_dec(v_fst_2828_);
                v___x_2832_ = lean_box(0);
                v___x_2833_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__1(v_snd_2829_, v___x_2832_);
                v___x_2834_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2834_, 0, v___x_2830_);
                lean_ctor_set(v___x_2834_, 1, v___x_2831_);
                lean_ctor_set(v___x_2834_, 2, v___x_2833_);
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 1, v_a_2821_);
                    lean_ctor_set(v___x_2826_, 0, v___x_2834_);
                    v___x_2836_ = v___x_2826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2834_);
                    lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2821_);
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
    mut v_as_x27_2845_: *mut LeanObject,
    mut v_b_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2845_) == 0 {
                    v___x_2850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2850_, 0, v_b_2846_);
                    return v___x_2850_;
                } else {
                    v_head_2851_ = lean_ctor_get(v_as_x27_2845_, 0);
                    v_tail_2852_ = lean_ctor_get(v_as_x27_2845_, 1);
                    lean_inc(v_head_2851_);
                    v___x_2853_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_head_2851_);
                    v___x_2854_ =
                        l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
                            v___x_2853_,
                            v___y_2847_,
                            v___y_2848_,
                        );
                    if lean_obj_tag(v___x_2854_) == 0 {
                        lean_dec_ref_known(v___x_2854_, 1);
                        v___x_2855_ = lean_box(0);
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
    mut v_as_x27_2857_: *mut LeanObject,
    mut v_b_2858_: *mut LeanObject,
    mut v___y_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2857_) == 0 {
                    v___x_2862_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2862_, 0, v_b_2858_);
                    return v___x_2862_;
                } else {
                    v_head_2863_ = lean_ctor_get(v_as_x27_2857_, 0);
                    v_tail_2864_ = lean_ctor_get(v_as_x27_2857_, 1);
                    v_snd_2865_ = lean_ctor_get(v_head_2863_, 1);
                    v___x_2866_ = lean_box(0);
                    v___x_2867_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(v_snd_2865_, v___x_2866_, v___y_2859_, v___y_2860_);
                    if lean_obj_tag(v___x_2867_) == 0 {
                        lean_dec_ref_known(v___x_2867_, 1);
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
-> *mut LeanObject {
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    v___x_2872_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__6;
    v___x_2873_ = lean_unsigned_to_nat(50);
    v___x_2874_ = lean_unsigned_to_nat(76);
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
    mut v_name_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
    mut v_a_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2901_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v_a_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2925_: u8 = 0;
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_a_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_val_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_val_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2983_: u8 = 0;
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3048_: u8 = 0;
    let mut v_name_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_val_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pending_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v_name_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_unused_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_a_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_name_2878_);
                v___x_2882_ = l___private_Lean_Replay_0__Lean_Environment_Replay_isTodo___redArg(
                    v_name_2878_,
                    v_a_2880_,
                );
                if lean_obj_tag(v___x_2882_) == 0 {
                    v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
                    v_isSharedCheck_3083_ = (!lean_is_exclusive(v___x_2882_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_2885_ = v___x_2882_;
                        v_isShared_2886_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2883_);
                        lean_dec(v___x_2882_);
                        v___x_2885_ = lean_box(0);
                        v_isShared_2886_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_2878_);
                    v_a_3084_ = lean_ctor_get(v___x_2882_, 0);
                    v_isSharedCheck_3091_ = (!lean_is_exclusive(v___x_2882_)) as u8;
                    if v_isSharedCheck_3091_ == 0 {
                        v___x_3086_ = v___x_2882_;
                        v_isShared_3087_ = v_isSharedCheck_3091_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_3084_);
                        lean_dec(v___x_2882_);
                        v___x_3086_ = lean_box(0);
                        v_isShared_3087_ = v_isSharedCheck_3091_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2887_ = (lean_unbox(v_a_2883_) as u8);
                lean_dec(v_a_2883_);
                if v___x_2887_ == 0 {
                    lean_dec(v_name_2878_);
                    v___x_2888_ = lean_box(0);
                    if v_isShared_2886_ == 0 {
                        lean_ctor_set(v___x_2885_, 0, v___x_2888_);
                        v___x_2890_ = v___x_2885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
                        v___x_2890_ = v_reuseFailAlloc_2891_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v_a_2879_, v_name_2878_);
                    if lean_obj_tag(v___x_2892_) == 1 {
                        v_val_2893_ = lean_ctor_get(v___x_2892_, 0);
                        v_isSharedCheck_3080_ = (!lean_is_exclusive(v___x_2892_)) as u8;
                        if v_isSharedCheck_3080_ == 0 {
                            v___x_2895_ = v___x_2892_;
                            v_isShared_2896_ = v_isSharedCheck_3080_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2893_);
                            lean_dec(v___x_2892_);
                            v___x_2895_ = lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_3080_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2892_);
                        lean_del_object(v___x_2885_);
                        lean_dec(v_name_2878_);
                        v___x_3081_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7_once), _init_l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__7);
                        v___x_3082_ = l_panic___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__10(v___x_3081_, v_a_2879_, v_a_2880_);
                        return v___x_3082_;
                    }
                }
            }
            2 => {
                return v___x_2890_;
            }
            3 => {
                lean_inc(v_val_2893_);
                v___x_2897_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_2893_);
                v___x_2898_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
                    v___x_2897_,
                    v_a_2879_,
                    v_a_2880_,
                );
                if lean_obj_tag(v___x_2898_) == 0 {
                    v_isSharedCheck_3078_ = (!lean_is_exclusive(v___x_2898_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v_unused_3079_ = lean_ctor_get(v___x_2898_, 0);
                        lean_dec(v_unused_3079_);
                        v___x_2900_ = v___x_2898_;
                        v_isShared_2901_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_2898_);
                        v___x_2900_ = lean_box(0);
                        v_isShared_2901_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2895_);
                    lean_dec(v_val_2893_);
                    lean_del_object(v___x_2885_);
                    lean_dec(v_name_2878_);
                    return v___x_2898_;
                }
            }
            4 => {
                v___x_2902_ = lean_st_ref_get(v_a_2880_);
                v_pending_2903_ = lean_ctor_get(v___x_2902_, 2);
                lean_inc(v_pending_2903_);
                lean_dec(v___x_2902_);
                v___x_2904_ = l_Lean_NameSet_contains(v_pending_2903_, v_name_2878_);
                lean_dec(v_pending_2903_);
                if v___x_2904_ == 0 {
                    lean_del_object(v___x_2900_);
                    lean_del_object(v___x_2895_);
                    lean_dec(v_val_2893_);
                    lean_dec(v_name_2878_);
                    v___x_2932_ = lean_box(0);
                    if v_isShared_2886_ == 0 {
                        lean_ctor_set(v___x_2885_, 0, v___x_2932_);
                        v___x_2934_ = v___x_2885_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
                        v___x_2934_ = v_reuseFailAlloc_2935_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_inc(v_name_2878_);
                    v___f_2936_ = lean_alloc_closure(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0___boxed as *mut core::ffi::c_void, 5, 1);
                    lean_closure_set(v___f_2936_, 0, v_name_2878_);
                    match lean_obj_tag(v_val_2893_) {
                        0 => {
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v_val_2937_ = lean_ctor_get(v_val_2893_, 0);
                            v_isSharedCheck_2948_ = (!lean_is_exclusive(v_val_2893_)) as u8;
                            if v_isSharedCheck_2948_ == 0 {
                                v___x_2939_ = v_val_2893_;
                                v_isShared_2940_ = v_isSharedCheck_2948_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_val_2937_);
                                lean_dec(v_val_2893_);
                                v___x_2939_ = lean_box(0);
                                v_isShared_2940_ = v_isSharedCheck_2948_;
                                state = 12;
                                continue;
                            }
                        }
                        1 => {
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v_val_2949_ = lean_ctor_get(v_val_2893_, 0);
                            v_isSharedCheck_2960_ = (!lean_is_exclusive(v_val_2893_)) as u8;
                            if v_isSharedCheck_2960_ == 0 {
                                v___x_2951_ = v_val_2893_;
                                v_isShared_2952_ = v_isSharedCheck_2960_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_val_2949_);
                                lean_dec(v_val_2893_);
                                v___x_2951_ = lean_box(0);
                                v_isShared_2952_ = v_isSharedCheck_2960_;
                                state = 14;
                                continue;
                            }
                        }
                        2 => {
                            v_val_2961_ = lean_ctor_get(v_val_2893_, 0);
                            lean_inc_ref_n(v_val_2961_, 2);
                            v___x_2962_ = lean_st_ref_get(v_a_2880_);
                            v_env_2963_ = lean_ctor_get(v___x_2962_, 0);
                            lean_inc_ref(v_env_2963_);
                            lean_dec(v___x_2962_);
                            lean_inc_ref(v___f_2936_);
                            v___f_2964_ = lean_alloc_closure(l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__1___boxed as *mut core::ffi::c_void, 6, 2);
                            lean_closure_set(v___f_2964_, 0, v_val_2961_);
                            lean_closure_set(v___f_2964_, 1, v___f_2936_);
                            v___x_2968_ = l_Lean_ConstantInfo_name(v_val_2893_);
                            lean_dec_ref_known(v_val_2893_, 1);
                            v___x_2969_ = lean_environment_find(v_env_2963_, v___x_2968_);
                            if lean_obj_tag(v___x_2969_) == 1 {
                                v_val_2970_ = lean_ctor_get(v___x_2969_, 0);
                                lean_inc(v_val_2970_);
                                if lean_obj_tag(v_val_2970_) == 2 {
                                    lean_dec_ref_known(v___x_2969_, 1);
                                    lean_dec_ref(v___f_2964_);
                                    v_toConstantVal_2971_ = lean_ctor_get(v_val_2961_, 0);
                                    v_val_2972_ = lean_ctor_get(v_val_2970_, 0);
                                    lean_inc_ref(v_val_2972_);
                                    lean_dec_ref_known(v_val_2970_, 1);
                                    v_toConstantVal_2973_ = lean_ctor_get(v_val_2972_, 0);
                                    lean_inc_ref(v_toConstantVal_2973_);
                                    v_all_2974_ = lean_ctor_get(v_val_2961_, 2);
                                    v_name_2975_ = lean_ctor_get(v_toConstantVal_2971_, 0);
                                    v_levelParams_2976_ = lean_ctor_get(v_toConstantVal_2971_, 1);
                                    v_type_2977_ = lean_ctor_get(v_toConstantVal_2971_, 2);
                                    v_all_2978_ = lean_ctor_get(v_val_2972_, 2);
                                    lean_inc(v_all_2978_);
                                    lean_dec_ref(v_val_2972_);
                                    v_name_2979_ = lean_ctor_get(v_toConstantVal_2973_, 0);
                                    lean_inc(v_name_2979_);
                                    v_levelParams_2980_ = lean_ctor_get(v_toConstantVal_2973_, 1);
                                    lean_inc(v_levelParams_2980_);
                                    v_type_2981_ = lean_ctor_get(v_toConstantVal_2973_, 2);
                                    lean_inc_ref(v_type_2981_);
                                    lean_dec_ref(v_toConstantVal_2973_);
                                    v___x_2990_ = lean_name_eq(v_name_2975_, v_name_2979_);
                                    lean_dec(v_name_2979_);
                                    if v___x_2990_ == 0 {
                                        lean_dec_ref(v_type_2981_);
                                        v___y_2983_ = v___x_2990_;
                                        state = 17;
                                        continue;
                                    } else {
                                        v___x_2991_ = lean_expr_eqv(v_type_2977_, v_type_2981_);
                                        lean_dec_ref(v_type_2981_);
                                        v___y_2983_ = v___x_2991_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_val_2970_);
                                    lean_dec_ref(v_val_2961_);
                                    lean_dec_ref(v___f_2936_);
                                    lean_del_object(v___x_2885_);
                                    v___x_2992_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(v___f_2964_, v___x_2969_, v_a_2879_, v_a_2880_);
                                    lean_dec_ref_known(v___x_2969_, 1);
                                    v___y_2921_ = v___x_2992_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_val_2961_);
                                lean_dec_ref(v___f_2936_);
                                lean_del_object(v___x_2885_);
                                v___x_2993_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__2(v___f_2964_, v___x_2969_, v_a_2879_, v_a_2880_);
                                lean_dec(v___x_2969_);
                                v___y_2921_ = v___x_2993_;
                                state = 8;
                                continue;
                            }
                        }
                        3 => {
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v_val_2994_ = lean_ctor_get(v_val_2893_, 0);
                            v_isSharedCheck_3005_ = (!lean_is_exclusive(v_val_2893_)) as u8;
                            if v_isSharedCheck_3005_ == 0 {
                                v___x_2996_ = v_val_2893_;
                                v_isShared_2997_ = v_isSharedCheck_3005_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_val_2994_);
                                lean_dec(v_val_2893_);
                                v___x_2996_ = lean_box(0);
                                v_isShared_2997_ = v_isSharedCheck_3005_;
                                state = 19;
                                continue;
                            }
                        }
                        4 => {
                            lean_dec_ref_known(v_val_2893_, 1);
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v___x_3006_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__3;
                            v___x_3007_ =
                                l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
                                    v___x_3006_,
                                    v_a_2879_,
                                    v_a_2880_,
                                );
                            if lean_obj_tag(v___x_3007_) == 0 {
                                lean_dec_ref_known(v___x_3007_, 1);
                                v___x_3008_ = lean_box(4);
                                v___x_3009_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v___x_3008_, v_a_2880_);
                                if lean_obj_tag(v___x_3009_) == 0 {
                                    v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
                                    lean_inc(v_a_3010_);
                                    lean_dec_ref_known(v___x_3009_, 1);
                                    v___x_3011_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(v_name_2878_, v_a_3010_, v_a_2879_, v_a_2880_);
                                    v___y_2921_ = v___x_3011_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_a_3012_ = lean_ctor_get(v___x_3009_, 0);
                                    lean_inc(v_a_3012_);
                                    lean_dec_ref_known(v___x_3009_, 1);
                                    v_a_2906_ = v_a_3012_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_3013_ = lean_ctor_get(v___x_3007_, 0);
                                lean_inc(v_a_3013_);
                                lean_dec_ref_known(v___x_3007_, 1);
                                v_a_2906_ = v_a_3013_;
                                state = 5;
                                continue;
                            }
                        }
                        5 => {
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v_val_3014_ = lean_ctor_get(v_val_2893_, 0);
                            lean_inc_ref(v_val_3014_);
                            lean_dec_ref_known(v_val_2893_, 1);
                            v_toConstantVal_3015_ = lean_ctor_get(v_val_3014_, 0);
                            lean_inc_ref(v_toConstantVal_3015_);
                            v_numParams_3016_ = lean_ctor_get(v_val_3014_, 1);
                            lean_inc(v_numParams_3016_);
                            v_all_3017_ = lean_ctor_get(v_val_3014_, 3);
                            lean_inc(v_all_3017_);
                            lean_dec_ref(v_val_3014_);
                            v___x_3018_ = lean_box(0);
                            v___x_3019_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_all_3017_, v___x_3018_, v_a_2879_);
                            if lean_obj_tag(v___x_3019_) == 0 {
                                v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
                                lean_inc(v_a_3020_);
                                lean_dec_ref_known(v___x_3019_, 1);
                                v___x_3021_ = lean_box(0);
                                v___x_3022_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(v_a_3020_, v___x_3021_, v_a_2880_);
                                if lean_obj_tag(v___x_3022_) == 0 {
                                    lean_dec_ref_known(v___x_3022_, 1);
                                    v___x_3023_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__7(v_a_3020_, v___x_3018_, v_a_2879_, v_a_2880_);
                                    if lean_obj_tag(v___x_3023_) == 0 {
                                        v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
                                        lean_inc(v_a_3024_);
                                        lean_dec_ref_known(v___x_3023_, 1);
                                        v___x_3025_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(v_a_3024_, v___x_3021_, v_a_2879_, v_a_2880_);
                                        if lean_obj_tag(v___x_3025_) == 0 {
                                            lean_dec_ref_known(v___x_3025_, 1);
                                            v_levelParams_3026_ =
                                                lean_ctor_get(v_toConstantVal_3015_, 1);
                                            lean_inc(v_levelParams_3026_);
                                            lean_dec_ref(v_toConstantVal_3015_);
                                            v___x_3027_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__9(v_a_3024_, v___x_3018_);
                                            v___x_3028_ = 0;
                                            v___x_3029_ = lean_alloc_ctor(6, 3, (1) as u32);
                                            lean_ctor_set(v___x_3029_, 0, v_levelParams_3026_);
                                            lean_ctor_set(v___x_3029_, 1, v_numParams_3016_);
                                            lean_ctor_set(v___x_3029_, 2, v___x_3027_);
                                            lean_ctor_set_uint8(
                                                v___x_3029_,
                                                (core::mem::size_of::<*mut LeanObject>() * 3)
                                                    as u32,
                                                v___x_3028_,
                                            );
                                            v___x_3030_ = l___private_Lean_Replay_0__Lean_Environment_Replay_addDecl___redArg(v___x_3029_, v_a_2880_);
                                            lean_dec_ref_known(v___x_3029_, 3);
                                            if lean_obj_tag(v___x_3030_) == 0 {
                                                v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
                                                lean_inc(v_a_3031_);
                                                lean_dec_ref_known(v___x_3030_, 1);
                                                v___x_3032_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___lam__0(v_name_2878_, v_a_3031_, v_a_2879_, v_a_2880_);
                                                v___y_2921_ = v___x_3032_;
                                                state = 8;
                                                continue;
                                            } else {
                                                v_a_3033_ = lean_ctor_get(v___x_3030_, 0);
                                                lean_inc(v_a_3033_);
                                                lean_dec_ref_known(v___x_3030_, 1);
                                                v_a_2906_ = v_a_3033_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_3024_);
                                            lean_dec(v_numParams_3016_);
                                            lean_dec_ref(v_toConstantVal_3015_);
                                            v_a_3034_ = lean_ctor_get(v___x_3025_, 0);
                                            lean_inc(v_a_3034_);
                                            lean_dec_ref_known(v___x_3025_, 1);
                                            v_a_2906_ = v_a_3034_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_numParams_3016_);
                                        lean_dec_ref(v_toConstantVal_3015_);
                                        v_a_3035_ = lean_ctor_get(v___x_3023_, 0);
                                        lean_inc(v_a_3035_);
                                        lean_dec_ref_known(v___x_3023_, 1);
                                        v_a_2906_ = v_a_3035_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3020_);
                                    lean_dec(v_numParams_3016_);
                                    lean_dec_ref(v_toConstantVal_3015_);
                                    v_a_3036_ = lean_ctor_get(v___x_3022_, 0);
                                    lean_inc(v_a_3036_);
                                    lean_dec_ref_known(v___x_3022_, 1);
                                    v_a_2906_ = v_a_3036_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_numParams_3016_);
                                lean_dec_ref(v_toConstantVal_3015_);
                                v_a_3037_ = lean_ctor_get(v___x_3019_, 0);
                                lean_inc(v_a_3037_);
                                lean_dec_ref_known(v___x_3019_, 1);
                                v_a_2906_ = v_a_3037_;
                                state = 5;
                                continue;
                            }
                        }
                        6 => {
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v_val_3038_ = lean_ctor_get(v_val_2893_, 0);
                            lean_inc_ref(v_val_3038_);
                            lean_dec_ref_known(v_val_2893_, 1);
                            v___x_3039_ = lean_st_ref_take(v_a_2880_);
                            v_toConstantVal_3040_ = lean_ctor_get(v_val_3038_, 0);
                            lean_inc_ref(v_toConstantVal_3040_);
                            lean_dec_ref(v_val_3038_);
                            v_env_3041_ = lean_ctor_get(v___x_3039_, 0);
                            v_remaining_3042_ = lean_ctor_get(v___x_3039_, 1);
                            v_pending_3043_ = lean_ctor_get(v___x_3039_, 2);
                            v_postponedConstructors_3044_ = lean_ctor_get(v___x_3039_, 3);
                            v_postponedRecursors_3045_ = lean_ctor_get(v___x_3039_, 4);
                            v_isSharedCheck_3057_ = (!lean_is_exclusive(v___x_3039_)) as u8;
                            if v_isSharedCheck_3057_ == 0 {
                                v___x_3047_ = v___x_3039_;
                                v_isShared_3048_ = v_isSharedCheck_3057_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_postponedRecursors_3045_);
                                lean_inc(v_postponedConstructors_3044_);
                                lean_inc(v_pending_3043_);
                                lean_inc(v_remaining_3042_);
                                lean_inc(v_env_3041_);
                                lean_dec(v___x_3039_);
                                v___x_3047_ = lean_box(0);
                                v_isShared_3048_ = v_isSharedCheck_3057_;
                                state = 21;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2885_);
                            v_val_3058_ = lean_ctor_get(v_val_2893_, 0);
                            lean_inc_ref(v_val_3058_);
                            lean_dec_ref_known(v_val_2893_, 1);
                            v___x_3059_ = lean_st_ref_take(v_a_2880_);
                            v_toConstantVal_3060_ = lean_ctor_get(v_val_3058_, 0);
                            lean_inc_ref(v_toConstantVal_3060_);
                            lean_dec_ref(v_val_3058_);
                            v_env_3061_ = lean_ctor_get(v___x_3059_, 0);
                            v_remaining_3062_ = lean_ctor_get(v___x_3059_, 1);
                            v_pending_3063_ = lean_ctor_get(v___x_3059_, 2);
                            v_postponedConstructors_3064_ = lean_ctor_get(v___x_3059_, 3);
                            v_postponedRecursors_3065_ = lean_ctor_get(v___x_3059_, 4);
                            v_isSharedCheck_3077_ = (!lean_is_exclusive(v___x_3059_)) as u8;
                            if v_isSharedCheck_3077_ == 0 {
                                v___x_3067_ = v___x_3059_;
                                v_isShared_3068_ = v_isSharedCheck_3077_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_postponedRecursors_3065_);
                                lean_inc(v_postponedConstructors_3064_);
                                lean_inc(v_pending_3063_);
                                lean_inc(v_remaining_3062_);
                                lean_inc(v_env_3061_);
                                lean_dec(v___x_3059_);
                                v___x_3067_ = lean_box(0);
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
                lean_dec_ref(v___x_2908_);
                v___x_2910_ =
                    l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___closed__1;
                v___x_2911_ = lean_string_append(v___x_2909_, v___x_2910_);
                v___x_2912_ = lean_io_error_to_string(v_a_2906_);
                v___x_2913_ = lean_string_append(v___x_2911_, v___x_2912_);
                lean_dec_ref(v___x_2912_);
                if v_isShared_2896_ == 0 {
                    lean_ctor_set_tag(v___x_2895_, 18);
                    lean_ctor_set(v___x_2895_, 0, v___x_2913_);
                    v___x_2915_ = v___x_2895_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = lean_alloc_ctor(18, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2913_);
                    v___x_2915_ = v_reuseFailAlloc_2919_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2901_ == 0 {
                    lean_ctor_set_tag(v___x_2900_, 1);
                    lean_ctor_set(v___x_2900_, 0, v___x_2915_);
                    v___x_2917_ = v___x_2900_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2917_;
            }
            8 => {
                if lean_obj_tag(v___y_2921_) == 0 {
                    lean_del_object(v___x_2900_);
                    lean_del_object(v___x_2895_);
                    lean_dec(v_name_2878_);
                    v_a_2922_ = lean_ctor_get(v___y_2921_, 0);
                    v_isSharedCheck_2930_ = (!lean_is_exclusive(v___y_2921_)) as u8;
                    if v_isSharedCheck_2930_ == 0 {
                        v___x_2924_ = v___y_2921_;
                        v_isShared_2925_ = v_isSharedCheck_2930_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2922_);
                        lean_dec(v___y_2921_);
                        v___x_2924_ = lean_box(0);
                        v_isShared_2925_ = v_isSharedCheck_2930_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_2931_ = lean_ctor_get(v___y_2921_, 0);
                    lean_inc(v_a_2931_);
                    lean_dec_ref_known(v___y_2921_, 1);
                    v_a_2906_ = v_a_2931_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                v_a_2926_ = lean_ctor_get(v_a_2922_, 0);
                lean_inc(v_a_2926_);
                lean_dec(v_a_2922_);
                if v_isShared_2925_ == 0 {
                    lean_ctor_set(v___x_2924_, 0, v_a_2926_);
                    v___x_2928_ = v___x_2924_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2926_);
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
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_val_2937_);
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
                lean_dec_ref(v___x_2942_);
                if lean_obj_tag(v___x_2943_) == 0 {
                    v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
                    lean_inc(v_a_2944_);
                    lean_dec_ref_known(v___x_2943_, 1);
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
                    v_a_2946_ = lean_ctor_get(v___x_2943_, 0);
                    lean_inc(v_a_2946_);
                    lean_dec_ref_known(v___x_2943_, 1);
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
                    v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_val_2949_);
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
                lean_dec_ref(v___x_2954_);
                if lean_obj_tag(v___x_2955_) == 0 {
                    v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
                    lean_inc(v_a_2956_);
                    lean_dec_ref_known(v___x_2955_, 1);
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
                    v_a_2958_ = lean_ctor_get(v___x_2955_, 0);
                    lean_inc(v_a_2958_);
                    lean_dec_ref_known(v___x_2955_, 1);
                    v_a_2906_ = v_a_2958_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                v___x_2966_ = lean_box(0);
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
                    lean_dec(v_levelParams_2980_);
                    lean_dec(v_all_2978_);
                    lean_del_object(v___x_2885_);
                    state = 16;
                    continue;
                } else {
                    v___x_2984_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_levelParams_2976_, v_levelParams_2980_);
                    lean_dec(v_levelParams_2980_);
                    if v___x_2984_ == 0 {
                        lean_dec(v_all_2978_);
                        lean_del_object(v___x_2885_);
                        state = 16;
                        continue;
                    } else {
                        v___x_2985_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_all_2974_, v_all_2978_);
                        lean_dec(v_all_2978_);
                        if v___x_2985_ == 0 {
                            lean_del_object(v___x_2885_);
                            state = 16;
                            continue;
                        } else {
                            lean_dec_ref(v_val_2961_);
                            lean_dec_ref(v___f_2936_);
                            lean_del_object(v___x_2900_);
                            lean_del_object(v___x_2895_);
                            lean_dec(v_name_2878_);
                            v___x_2986_ = lean_box(0);
                            if v_isShared_2886_ == 0 {
                                lean_ctor_set(v___x_2885_, 0, v___x_2986_);
                                v___x_2988_ = v___x_2885_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2986_);
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
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_val_2994_);
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
                lean_dec_ref(v___x_2999_);
                if lean_obj_tag(v___x_3000_) == 0 {
                    v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
                    lean_inc(v_a_3001_);
                    lean_dec_ref_known(v___x_3000_, 1);
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
                    v_a_3003_ = lean_ctor_get(v___x_3000_, 0);
                    lean_inc(v_a_3003_);
                    lean_dec_ref_known(v___x_3000_, 1);
                    v_a_2906_ = v_a_3003_;
                    state = 5;
                    continue;
                }
            }
            21 => {
                v_name_3049_ = lean_ctor_get(v_toConstantVal_3040_, 0);
                lean_inc(v_name_3049_);
                lean_dec_ref(v_toConstantVal_3040_);
                v___x_3050_ = l_Lean_NameSet_insert(v_postponedConstructors_3044_, v_name_3049_);
                if v_isShared_3048_ == 0 {
                    lean_ctor_set(v___x_3047_, 3, v___x_3050_);
                    v___x_3052_ = v___x_3047_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_env_3041_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_remaining_3042_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_pending_3043_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 3, v___x_3050_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_postponedRecursors_3045_);
                    v___x_3052_ = v_reuseFailAlloc_3056_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_3053_ = lean_st_ref_set(v_a_2880_, v___x_3052_);
                v___x_3054_ = lean_box(0);
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
                v_name_3069_ = lean_ctor_get(v_toConstantVal_3060_, 0);
                lean_inc(v_name_3069_);
                lean_dec_ref(v_toConstantVal_3060_);
                v___x_3070_ = l_Lean_NameSet_insert(v_postponedRecursors_3065_, v_name_3069_);
                if v_isShared_3068_ == 0 {
                    lean_ctor_set(v___x_3067_, 4, v___x_3070_);
                    v___x_3072_ = v___x_3067_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_env_3061_);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_remaining_3062_);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_pending_3063_);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_postponedConstructors_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___x_3070_);
                    v___x_3072_ = v_reuseFailAlloc_3076_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3073_ = lean_st_ref_set(v_a_2880_, v___x_3072_);
                v___x_3074_ = lean_box(0);
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
                    v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
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
    mut v_init_3092_: *mut LeanObject,
    mut v_x_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3093_) == 0 {
                    v_k_3097_ = lean_ctor_get(v_x_3093_, 1);
                    lean_inc(v_k_3097_);
                    v_l_3098_ = lean_ctor_get(v_x_3093_, 3);
                    lean_inc(v_l_3098_);
                    v_r_3099_ = lean_ctor_get(v_x_3093_, 4);
                    lean_inc(v_r_3099_);
                    lean_dec_ref_known(v_x_3093_, 5);
                    v___x_3100_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v_init_3092_, v_l_3098_, v___y_3094_, v___y_3095_);
                    if lean_obj_tag(v___x_3100_) == 0 {
                        lean_dec_ref_known(v___x_3100_, 1);
                        v___x_3101_ =
                            l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
                                v_k_3097_,
                                v___y_3094_,
                                v___y_3095_,
                            );
                        if lean_obj_tag(v___x_3101_) == 0 {
                            lean_dec_ref_known(v___x_3101_, 1);
                            v___x_3102_ = lean_box(0);
                            v_init_3092_ = v___x_3102_;
                            v_x_3093_ = v_r_3099_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_r_3099_);
                            v_a_3104_ = lean_ctor_get(v___x_3101_, 0);
                            v_isSharedCheck_3111_ = (!lean_is_exclusive(v___x_3101_)) as u8;
                            if v_isSharedCheck_3111_ == 0 {
                                v___x_3106_ = v___x_3101_;
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3104_);
                                lean_dec(v___x_3101_);
                                v___x_3106_ = lean_box(0);
                                v_isShared_3107_ = v_isSharedCheck_3111_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_r_3099_);
                        lean_dec(v_k_3097_);
                        return v___x_3100_;
                    }
                } else {
                    v___x_3112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3112_, 0, v_init_3092_);
                    v___x_3113_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3113_, 0, v___x_3112_);
                    return v___x_3113_;
                }
            }
            1 => {
                if v_isShared_3107_ == 0 {
                    v___x_3109_ = v___x_3106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
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
    mut v_names_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_unused_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3118_ = lean_box(0);
                v___x_3119_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v___x_3118_, v_names_3114_, v_a_3115_, v_a_3116_);
                if lean_obj_tag(v___x_3119_) == 0 {
                    v_isSharedCheck_3126_ = (!lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3126_ == 0 {
                        v_unused_3127_ = lean_ctor_get(v___x_3119_, 0);
                        lean_dec(v_unused_3127_);
                        v___x_3121_ = v___x_3119_;
                        v_isShared_3122_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3119_);
                        v___x_3121_ = lean_box(0);
                        v_isShared_3122_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3128_ = lean_ctor_get(v___x_3119_, 0);
                    v_isSharedCheck_3135_ = (!lean_is_exclusive(v___x_3119_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3130_ = v___x_3119_;
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3128_);
                        lean_dec(v___x_3119_);
                        v___x_3130_ = lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3135_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3122_ == 0 {
                    lean_ctor_set(v___x_3121_, 0, v___x_3118_);
                    v___x_3124_ = v___x_3121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3118_);
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
                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
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
    mut v_names_3136_: *mut LeanObject,
    mut v_a_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3140_: *mut LeanObject = core::ptr::null_mut();
    v_res_3140_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstants(
        v_names_3136_,
        v_a_3137_,
        v_a_3138_,
    );
    lean_dec(v_a_3138_);
    lean_dec_ref(v_a_3137_);
    return v_res_3140_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg___boxed(
    mut v_as_x27_3141_: *mut LeanObject,
    mut v_b_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3146_: *mut LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_3141_, v_b_3142_, v___y_3143_, v___y_3144_);
    lean_dec(v___y_3144_);
    lean_dec_ref(v___y_3143_);
    lean_dec(v_as_x27_3141_);
    return v_res_3146_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg___boxed(
    mut v_as_x27_3147_: *mut LeanObject,
    mut v_b_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_3147_, v_b_3148_, v___y_3149_, v___y_3150_);
    lean_dec(v___y_3150_);
    lean_dec_ref(v___y_3149_);
    lean_dec(v_as_x27_3147_);
    return v_res_3152_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12___boxed(
    mut v_init_3153_: *mut LeanObject,
    mut v_x_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3158_: *mut LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v_init_3153_, v_x_3154_, v___y_3155_, v___y_3156_);
    lean_dec(v___y_3156_);
    lean_dec_ref(v___y_3155_);
    return v_res_3158_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant___boxed(
    mut v_name_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3163_: *mut LeanObject = core::ptr::null_mut();
    v_res_3163_ = l___private_Lean_Replay_0__Lean_Environment_Replay_replayConstant(
        v_name_3159_,
        v_a_3160_,
        v_a_3161_,
    );
    lean_dec(v_a_3161_);
    lean_dec_ref(v_a_3160_);
    return v_res_3163_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2(
    mut v_x_3164_: *mut LeanObject,
    mut v_x_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    v___x_3169_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___redArg(v_x_3164_, v_x_3165_, v___y_3166_);
    return v___x_3169_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2___boxed(
    mut v_x_3170_: *mut LeanObject,
    mut v_x_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3175_: *mut LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__2(v_x_3170_, v_x_3171_, v___y_3172_, v___y_3173_);
    lean_dec(v___y_3173_);
    lean_dec_ref(v___y_3172_);
    return v_res_3175_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3(
    mut v_00_u03b2_3176_: *mut LeanObject,
    mut v_m_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v_m_3177_, v_a_3178_);
    return v___x_3179_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___boxed(
    mut v_00_u03b2_3180_: *mut LeanObject,
    mut v_m_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3183_: *mut LeanObject = core::ptr::null_mut();
    v_res_3183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3(v_00_u03b2_3180_, v_m_3181_, v_a_3182_);
    lean_dec(v_a_3182_);
    lean_dec_ref(v_m_3181_);
    return v_res_3183_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5(
    mut v_as_3184_: *mut LeanObject,
    mut v_as_x27_3185_: *mut LeanObject,
    mut v_b_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    v___x_3191_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_3185_, v_b_3186_, v___y_3188_, v___y_3189_);
    return v___x_3191_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5___boxed(
    mut v_as_3192_: *mut LeanObject,
    mut v_as_x27_3193_: *mut LeanObject,
    mut v_b_3194_: *mut LeanObject,
    mut v_a_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3199_: *mut LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__5(v_as_3192_, v_as_x27_3193_, v_b_3194_, v_a_3195_, v___y_3196_, v___y_3197_);
    lean_dec(v___y_3197_);
    lean_dec_ref(v___y_3196_);
    lean_dec(v_as_x27_3193_);
    lean_dec(v_as_3192_);
    return v_res_3199_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6(
    mut v_as_3200_: *mut LeanObject,
    mut v_as_x27_3201_: *mut LeanObject,
    mut v_b_3202_: *mut LeanObject,
    mut v_a_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_3201_, v_b_3202_, v___y_3205_);
    return v___x_3207_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6___boxed(
    mut v_as_3208_: *mut LeanObject,
    mut v_as_x27_3209_: *mut LeanObject,
    mut v_b_3210_: *mut LeanObject,
    mut v_a_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3215_: *mut LeanObject = core::ptr::null_mut();
    v_res_3215_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__6(v_as_3208_, v_as_x27_3209_, v_b_3210_, v_a_3211_, v___y_3212_, v___y_3213_);
    lean_dec(v___y_3213_);
    lean_dec_ref(v___y_3212_);
    lean_dec(v_as_x27_3209_);
    lean_dec(v_as_3208_);
    return v_res_3215_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8(
    mut v_as_3216_: *mut LeanObject,
    mut v_as_x27_3217_: *mut LeanObject,
    mut v_b_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    v___x_3223_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_3217_, v_b_3218_, v___y_3220_, v___y_3221_);
    return v___x_3223_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8___boxed(
    mut v_as_3224_: *mut LeanObject,
    mut v_as_x27_3225_: *mut LeanObject,
    mut v_b_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3231_: *mut LeanObject = core::ptr::null_mut();
    v_res_3231_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__8(v_as_3224_, v_as_x27_3225_, v_b_3226_, v_a_3227_, v___y_3228_, v___y_3229_);
    lean_dec(v___y_3229_);
    lean_dec_ref(v___y_3228_);
    lean_dec(v_as_x27_3225_);
    lean_dec(v_as_3224_);
    return v_res_3231_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4(
    mut v_00_u03b2_3232_: *mut LeanObject,
    mut v_a_3233_: *mut LeanObject,
    mut v_x_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    v___x_3235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_3233_, v_x_3234_);
    return v___x_3235_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4___boxed(
    mut v_00_u03b2_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
    mut v_x_3238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3239_: *mut LeanObject = core::ptr::null_mut();
    v_res_3239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3_spec__4(v_00_u03b2_3236_, v_a_3237_, v_x_3238_);
    lean_dec(v_x_3238_);
    lean_dec(v_a_3237_);
    return v_res_3239_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(
    mut v_init_3242_: *mut LeanObject,
    mut v_x_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_unused_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3243_) == 0 {
                    v_k_3247_ = lean_ctor_get(v_x_3243_, 1);
                    lean_inc(v_k_3247_);
                    v_l_3248_ = lean_ctor_get(v_x_3243_, 3);
                    lean_inc(v_l_3248_);
                    v_r_3249_ = lean_ctor_get(v_x_3243_, 4);
                    lean_inc(v_r_3249_);
                    lean_dec_ref_known(v_x_3243_, 5);
                    v___x_3257_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(v_init_3242_, v_l_3248_, v___y_3244_, v___y_3245_);
                    if lean_obj_tag(v___x_3257_) == 0 {
                        v_isSharedCheck_3280_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3280_ == 0 {
                            v_unused_3281_ = lean_ctor_get(v___x_3257_, 0);
                            lean_dec(v_unused_3281_);
                            v___x_3259_ = v___x_3257_;
                            v_isShared_3260_ = v_isSharedCheck_3280_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3257_);
                            v___x_3259_ = lean_box(0);
                            v_isShared_3260_ = v_isSharedCheck_3280_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_r_3249_);
                        lean_dec(v_k_3247_);
                        return v___x_3257_;
                    }
                } else {
                    v___x_3282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3282_, 0, v_init_3242_);
                    v___x_3283_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3283_, 0, v___x_3282_);
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
                lean_dec_ref(v___x_3253_);
                v___x_3255_ = lean_mk_io_user_error(v___x_3254_);
                v___x_3256_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3256_, 0, v___x_3255_);
                return v___x_3256_;
            }
            2 => {
                v___x_3261_ = lean_st_ref_get(v___y_3245_);
                v_env_3262_ = lean_ctor_get(v___x_3261_, 0);
                lean_inc_ref(v_env_3262_);
                lean_dec(v___x_3261_);
                lean_inc(v_k_3247_);
                v___x_3263_ = lean_environment_find(v_env_3262_, v_k_3247_);
                if lean_obj_tag(v___x_3263_) == 1 {
                    v_val_3264_ = lean_ctor_get(v___x_3263_, 0);
                    lean_inc(v_val_3264_);
                    lean_dec_ref_known(v___x_3263_, 1);
                    if lean_obj_tag(v_val_3264_) == 6 {
                        v_val_3265_ = lean_ctor_get(v_val_3264_, 0);
                        lean_inc_ref(v_val_3265_);
                        lean_dec_ref_known(v_val_3264_, 1);
                        v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v___y_3244_, v_k_3247_);
                        if lean_obj_tag(v___x_3266_) == 1 {
                            v_val_3267_ = lean_ctor_get(v___x_3266_, 0);
                            lean_inc(v_val_3267_);
                            lean_dec_ref_known(v___x_3266_, 1);
                            if lean_obj_tag(v_val_3267_) == 6 {
                                v_val_3268_ = lean_ctor_get(v_val_3267_, 0);
                                lean_inc_ref(v_val_3268_);
                                lean_dec_ref_known(v_val_3267_, 1);
                                v___x_3269_ =
                                    l_Lean_instBEqConstructorVal_beq(v_val_3265_, v_val_3268_);
                                lean_dec_ref(v_val_3268_);
                                lean_dec_ref(v_val_3265_);
                                if v___x_3269_ == 0 {
                                    lean_dec(v_r_3249_);
                                    v___x_3270_ = 1;
                                    v___x_3271_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1;
                                    v___x_3272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_3247_, v___x_3270_);
                                    v___x_3273_ = lean_string_append(v___x_3271_, v___x_3272_);
                                    lean_dec_ref(v___x_3272_);
                                    v___x_3274_ = lean_mk_io_user_error(v___x_3273_);
                                    if v_isShared_3260_ == 0 {
                                        lean_ctor_set_tag(v___x_3259_, 1);
                                        lean_ctor_set(v___x_3259_, 0, v___x_3274_);
                                        v___x_3276_ = v___x_3259_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
                                        v___x_3276_ = v_reuseFailAlloc_3277_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_3259_);
                                    lean_dec(v_k_3247_);
                                    v___x_3278_ = lean_box(0);
                                    v_init_3242_ = v___x_3278_;
                                    v_x_3243_ = v_r_3249_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_3267_);
                                lean_dec_ref(v_val_3265_);
                                lean_del_object(v___x_3259_);
                                lean_dec(v_r_3249_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3266_);
                            lean_dec_ref(v_val_3265_);
                            lean_del_object(v___x_3259_);
                            lean_dec(v_r_3249_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3264_);
                        lean_del_object(v___x_3259_);
                        lean_dec(v_r_3249_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3263_);
                    lean_del_object(v___x_3259_);
                    lean_dec(v_r_3249_);
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
    mut v_init_3284_: *mut LeanObject,
    mut v_x_3285_: *mut LeanObject,
    mut v___y_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3289_: *mut LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(v_init_3284_, v_x_3285_, v___y_3286_, v___y_3287_);
    lean_dec(v___y_3287_);
    lean_dec_ref(v___y_3286_);
    return v_res_3289_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors(
    mut v_a_3290_: *mut LeanObject,
    mut v_a_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedConstructors_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_unused_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3293_ = lean_st_ref_get(v_a_3291_);
                v_postponedConstructors_3294_ = lean_ctor_get(v___x_3293_, 3);
                lean_inc(v_postponedConstructors_3294_);
                lean_dec(v___x_3293_);
                v___x_3295_ = lean_box(0);
                v___x_3296_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors_spec__0(v___x_3295_, v_postponedConstructors_3294_, v_a_3290_, v_a_3291_);
                if lean_obj_tag(v___x_3296_) == 0 {
                    v_isSharedCheck_3303_ = (!lean_is_exclusive(v___x_3296_)) as u8;
                    if v_isSharedCheck_3303_ == 0 {
                        v_unused_3304_ = lean_ctor_get(v___x_3296_, 0);
                        lean_dec(v_unused_3304_);
                        v___x_3298_ = v___x_3296_;
                        v_isShared_3299_ = v_isSharedCheck_3303_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3296_);
                        v___x_3298_ = lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3303_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3305_ = lean_ctor_get(v___x_3296_, 0);
                    v_isSharedCheck_3312_ = (!lean_is_exclusive(v___x_3296_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v___x_3307_ = v___x_3296_;
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3305_);
                        lean_dec(v___x_3296_);
                        v___x_3307_ = lean_box(0);
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3299_ == 0 {
                    lean_ctor_set(v___x_3298_, 0, v___x_3295_);
                    v___x_3301_ = v___x_3298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3295_);
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
                    v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
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
    mut v_a_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3316_: *mut LeanObject = core::ptr::null_mut();
    v_res_3316_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors(
        v_a_3313_, v_a_3314_,
    );
    lean_dec(v_a_3314_);
    lean_dec_ref(v_a_3313_);
    return v_res_3316_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(
    mut v_init_3319_: *mut LeanObject,
    mut v_x_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut v_unused_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3320_) == 0 {
                    v_k_3324_ = lean_ctor_get(v_x_3320_, 1);
                    lean_inc(v_k_3324_);
                    v_l_3325_ = lean_ctor_get(v_x_3320_, 3);
                    lean_inc(v_l_3325_);
                    v_r_3326_ = lean_ctor_get(v_x_3320_, 4);
                    lean_inc(v_r_3326_);
                    lean_dec_ref_known(v_x_3320_, 5);
                    v___x_3334_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(v_init_3319_, v_l_3325_, v___y_3321_, v___y_3322_);
                    if lean_obj_tag(v___x_3334_) == 0 {
                        v_isSharedCheck_3357_ = (!lean_is_exclusive(v___x_3334_)) as u8;
                        if v_isSharedCheck_3357_ == 0 {
                            v_unused_3358_ = lean_ctor_get(v___x_3334_, 0);
                            lean_dec(v_unused_3358_);
                            v___x_3336_ = v___x_3334_;
                            v_isShared_3337_ = v_isSharedCheck_3357_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3334_);
                            v___x_3336_ = lean_box(0);
                            v_isShared_3337_ = v_isSharedCheck_3357_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_r_3326_);
                        lean_dec(v_k_3324_);
                        return v___x_3334_;
                    }
                } else {
                    v___x_3359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3359_, 0, v_init_3319_);
                    v___x_3360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3360_, 0, v___x_3359_);
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
                lean_dec_ref(v___x_3330_);
                v___x_3332_ = lean_mk_io_user_error(v___x_3331_);
                v___x_3333_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3333_, 0, v___x_3332_);
                return v___x_3333_;
            }
            2 => {
                v___x_3338_ = lean_st_ref_get(v___y_3322_);
                v_env_3339_ = lean_ctor_get(v___x_3338_, 0);
                lean_inc_ref(v_env_3339_);
                lean_dec(v___x_3338_);
                lean_inc(v_k_3324_);
                v___x_3340_ = lean_environment_find(v_env_3339_, v_k_3324_);
                if lean_obj_tag(v___x_3340_) == 1 {
                    v_val_3341_ = lean_ctor_get(v___x_3340_, 0);
                    lean_inc(v_val_3341_);
                    lean_dec_ref_known(v___x_3340_, 1);
                    if lean_obj_tag(v_val_3341_) == 7 {
                        v_val_3342_ = lean_ctor_get(v_val_3341_, 0);
                        lean_inc_ref(v_val_3342_);
                        lean_dec_ref_known(v_val_3341_, 1);
                        v___x_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__3___redArg(v___y_3321_, v_k_3324_);
                        if lean_obj_tag(v___x_3343_) == 1 {
                            v_val_3344_ = lean_ctor_get(v___x_3343_, 0);
                            lean_inc(v_val_3344_);
                            lean_dec_ref_known(v___x_3343_, 1);
                            if lean_obj_tag(v_val_3344_) == 7 {
                                v_val_3345_ = lean_ctor_get(v_val_3344_, 0);
                                lean_inc_ref(v_val_3345_);
                                lean_dec_ref_known(v_val_3344_, 1);
                                v___x_3346_ =
                                    l_Lean_instBEqRecursorVal_beq(v_val_3342_, v_val_3345_);
                                lean_dec_ref(v_val_3345_);
                                lean_dec_ref(v_val_3342_);
                                if v___x_3346_ == 0 {
                                    lean_dec(v_r_3326_);
                                    v___x_3347_ = 1;
                                    v___x_3348_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1;
                                    v___x_3349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_3324_, v___x_3347_);
                                    v___x_3350_ = lean_string_append(v___x_3348_, v___x_3349_);
                                    lean_dec_ref(v___x_3349_);
                                    v___x_3351_ = lean_mk_io_user_error(v___x_3350_);
                                    if v_isShared_3337_ == 0 {
                                        lean_ctor_set_tag(v___x_3336_, 1);
                                        lean_ctor_set(v___x_3336_, 0, v___x_3351_);
                                        v___x_3353_ = v___x_3336_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
                                        v___x_3353_ = v_reuseFailAlloc_3354_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_3336_);
                                    lean_dec(v_k_3324_);
                                    v___x_3355_ = lean_box(0);
                                    v_init_3319_ = v___x_3355_;
                                    v_x_3320_ = v_r_3326_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_3344_);
                                lean_dec_ref(v_val_3342_);
                                lean_del_object(v___x_3336_);
                                lean_dec(v_r_3326_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3343_);
                            lean_dec_ref(v_val_3342_);
                            lean_del_object(v___x_3336_);
                            lean_dec(v_r_3326_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3341_);
                        lean_del_object(v___x_3336_);
                        lean_dec(v_r_3326_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3340_);
                    lean_del_object(v___x_3336_);
                    lean_dec(v_r_3326_);
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
    mut v_init_3361_: *mut LeanObject,
    mut v_x_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3366_: *mut LeanObject = core::ptr::null_mut();
    v_res_3366_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(v_init_3361_, v_x_3362_, v___y_3363_, v___y_3364_);
    lean_dec(v___y_3364_);
    lean_dec_ref(v___y_3363_);
    return v_res_3366_;
}
pub unsafe fn l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors(
    mut v_a_3367_: *mut LeanObject,
    mut v_a_3368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponedRecursors_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut v_unused_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3385_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3370_ = lean_st_ref_get(v_a_3368_);
                v_postponedRecursors_3371_ = lean_ctor_get(v___x_3370_, 4);
                lean_inc(v_postponedRecursors_3371_);
                lean_dec(v___x_3370_);
                v___x_3372_ = lean_box(0);
                v___x_3373_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors_spec__0(v___x_3372_, v_postponedRecursors_3371_, v_a_3367_, v_a_3368_);
                if lean_obj_tag(v___x_3373_) == 0 {
                    v_isSharedCheck_3380_ = (!lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3380_ == 0 {
                        v_unused_3381_ = lean_ctor_get(v___x_3373_, 0);
                        lean_dec(v_unused_3381_);
                        v___x_3375_ = v___x_3373_;
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3373_);
                        v___x_3375_ = lean_box(0);
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3382_ = lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3389_ = (!lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3389_ == 0 {
                        v___x_3384_ = v___x_3373_;
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3382_);
                        lean_dec(v___x_3373_);
                        v___x_3384_ = lean_box(0);
                        v_isShared_3385_ = v_isSharedCheck_3389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3376_ == 0 {
                    lean_ctor_set(v___x_3375_, 0, v___x_3372_);
                    v___x_3378_ = v___x_3375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3372_);
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
                    v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
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
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_res_3393_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedRecursors(
        v_a_3390_, v_a_3391_,
    );
    lean_dec(v_a_3391_);
    lean_dec_ref(v_a_3390_);
    return v_res_3393_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
    mut v_as_x27_3394_: *mut LeanObject,
    mut v_b_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3394_) == 0 {
                    v___x_3397_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3397_, 0, v_b_3395_);
                    return v___x_3397_;
                } else {
                    v_head_3398_ = lean_ctor_get(v_as_x27_3394_, 0);
                    v_tail_3399_ = lean_ctor_get(v_as_x27_3394_, 1);
                    v_fst_3400_ = lean_ctor_get(v_head_3398_, 0);
                    v_snd_3401_ = lean_ctor_get(v_head_3398_, 1);
                    v___x_3402_ = l_Lean_ConstantInfo_isUnsafe(v_snd_3401_);
                    if v___x_3402_ == 0 {
                        v___x_3403_ = l_Lean_ConstantInfo_isPartial(v_snd_3401_);
                        if v___x_3403_ == 0 {
                            lean_inc(v_fst_3400_);
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
    mut v_as_x27_3408_: *mut LeanObject,
    mut v_b_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3411_: *mut LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
        v_as_x27_3408_,
        v_b_3409_,
    );
    lean_dec(v_as_x27_3408_);
    return v_res_3411_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(
    mut v_x_3412_: *mut LeanObject,
    mut v_x_3413_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3413_) == 0 {
        lean_inc(v_x_3412_);
        return v_x_3412_;
    } else {
        let mut v_key_3414_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_3415_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_3416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
        v_key_3414_ = lean_ctor_get(v_x_3413_, 0);
        v_value_3415_ = lean_ctor_get(v_x_3413_, 1);
        v_tail_3416_ = lean_ctor_get(v_x_3413_, 2);
        v___x_3417_ =
            l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(
                v_x_3412_,
                v_tail_3416_,
            );
        lean_inc(v_value_3415_);
        lean_inc(v_key_3414_);
        v___x_3418_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3418_, 0, v_key_3414_);
        lean_ctor_set(v___x_3418_, 1, v_value_3415_);
        v___x_3419_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3419_, 0, v___x_3418_);
        lean_ctor_set(v___x_3419_, 1, v___x_3417_);
        return v___x_3419_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1___boxed(
    mut v_x_3420_: *mut LeanObject,
    mut v_x_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3422_: *mut LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_spec__1(
        v_x_3420_, v_x_3421_,
    );
    lean_dec(v_x_3421_);
    lean_dec(v_x_3420_);
    return v_res_3422_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_spec__2(
    mut v_as_3423_: *mut LeanObject,
    mut v_i_3424_: usize,
    mut v_stop_3425_: usize,
    mut v_b_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: usize = 0;
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec(v_b_3426_);
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
    mut v_as_3433_: *mut LeanObject,
    mut v_i_3434_: *mut LeanObject,
    mut v_stop_3435_: *mut LeanObject,
    mut v_b_3436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3437_: usize = 0;
    let mut v_stop_boxed_3438_: usize = 0;
    let mut v_res_3439_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3437_ = lean_unbox_usize(v_i_3434_);
    lean_dec(v_i_3434_);
    v_stop_boxed_3438_ = lean_unbox_usize(v_stop_3435_);
    lean_dec(v_stop_3435_);
    v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_spec__2(v_as_3433_, v_i_boxed_3437_, v_stop_boxed_3438_, v_b_3436_);
    lean_dec_ref(v_as_3433_);
    return v_res_3439_;
}
pub unsafe fn l_Lean_Environment_replay(
    mut v_newConstants_3440_: *mut LeanObject,
    mut v_env_3441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_unused_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_buckets_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3465_ = lean_ctor_get(v_newConstants_3440_, 1);
                v_remaining_3466_ = l_Lean_NameSet_empty;
                v___x_3486_ = lean_box(0);
                v___x_3487_ = lean_array_get_size(v_buckets_3465_);
                v___x_3488_ = lean_unsigned_to_nat(0);
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
                if lean_obj_tag(v___y_3445_) == 0 {
                    v_isSharedCheck_3455_ = (!lean_is_exclusive(v___y_3445_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v_unused_3456_ = lean_ctor_get(v___y_3445_, 0);
                        lean_dec(v_unused_3456_);
                        v___x_3447_ = v___y_3445_;
                        v_isShared_3448_ = v_isSharedCheck_3455_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_3445_);
                        v___x_3447_ = lean_box(0);
                        v_isShared_3448_ = v_isSharedCheck_3455_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_3444_);
                    v_a_3457_ = lean_ctor_get(v___y_3445_, 0);
                    v_isSharedCheck_3464_ = (!lean_is_exclusive(v___y_3445_)) as u8;
                    if v_isSharedCheck_3464_ == 0 {
                        v___x_3459_ = v___y_3445_;
                        v_isShared_3460_ = v_isSharedCheck_3464_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3457_);
                        lean_dec(v___y_3445_);
                        v___x_3459_ = lean_box(0);
                        v_isShared_3460_ = v_isSharedCheck_3464_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3449_ = lean_st_ref_get(v___y_3444_);
                lean_dec(v___y_3444_);
                v_env_3450_ = lean_ctor_get(v___x_3449_, 0);
                lean_inc_ref(v_env_3450_);
                lean_dec(v___x_3449_);
                v___x_3451_ = lean_elab_environment_of_kernel_env(v_env_3450_);
                if v_isShared_3448_ == 0 {
                    lean_ctor_set(v___x_3447_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
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
                    v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
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
                lean_dec(v___y_3468_);
                v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
                lean_inc_n(v_a_3470_, 2);
                lean_dec_ref(v___x_3469_);
                v___x_3471_ = lean_elab_environment_to_kernel_env(v_env_3441_);
                v___x_3472_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3472_, 0, v___x_3471_);
                lean_ctor_set(v___x_3472_, 1, v_a_3470_);
                lean_ctor_set(v___x_3472_, 2, v_remaining_3466_);
                lean_ctor_set(v___x_3472_, 3, v_remaining_3466_);
                lean_ctor_set(v___x_3472_, 4, v_remaining_3466_);
                v___x_3473_ = lean_st_mk_ref(v___x_3472_);
                v___x_3474_ = lean_box(0);
                v___x_3475_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstants_spec__12(v___x_3474_, v_a_3470_, v_newConstants_3440_, v___x_3473_);
                if lean_obj_tag(v___x_3475_) == 0 {
                    lean_dec_ref_known(v___x_3475_, 1);
                    v___x_3476_ = l___private_Lean_Replay_0__Lean_Environment_Replay_checkPostponedConstructors(v_newConstants_3440_, v___x_3473_);
                    if lean_obj_tag(v___x_3476_) == 0 {
                        lean_dec_ref_known(v___x_3476_, 1);
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
                    lean_dec(v___x_3473_);
                    v_a_3478_ = lean_ctor_get(v___x_3475_, 0);
                    v_isSharedCheck_3485_ = (!lean_is_exclusive(v___x_3475_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v___x_3480_ = v___x_3475_;
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3478_);
                        lean_dec(v___x_3475_);
                        v___x_3480_ = lean_box(0);
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
                    v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
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
    mut v_newConstants_3493_: *mut LeanObject,
    mut v_env_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3496_: *mut LeanObject = core::ptr::null_mut();
    v_res_3496_ = l_Lean_Environment_replay(v_newConstants_3493_, v_env_3494_);
    lean_dec_ref(v_newConstants_3493_);
    return v_res_3496_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0(
    mut v_as_3497_: *mut LeanObject,
    mut v_as_x27_3498_: *mut LeanObject,
    mut v_b_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___redArg(
        v_as_x27_3498_,
        v_b_3499_,
    );
    return v___x_3502_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0___boxed(
    mut v_as_3503_: *mut LeanObject,
    mut v_as_x27_3504_: *mut LeanObject,
    mut v_b_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3508_: *mut LeanObject = core::ptr::null_mut();
    v_res_3508_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_spec__0(
        v_as_3503_,
        v_as_x27_3504_,
        v_b_3505_,
        v_a_3506_,
    );
    lean_dec(v_as_x27_3504_);
    lean_dec(v_as_3503_);
    return v_res_3508_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Replay(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FoldConsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Replay(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Replay(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_FoldConsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Replay(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Replay(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Replay(builtin);
}
