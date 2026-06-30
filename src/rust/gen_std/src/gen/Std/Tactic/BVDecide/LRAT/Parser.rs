// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Parser
// Imports: Init.System.IO Std.Tactic.BVDecide.LRAT.Actions Std.Internal.Parsec
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_uget_borrowed, lean_byte_array_fget, lean_byte_array_push, lean_byte_array_size,
    lean_int_dec_lt, lean_int_neg, lean_mk_empty_byte_array, lean_nat_abs, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_string_append, lean_string_to_utf8, lean_uint8_complement,
    lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint8_land, lean_uint8_lor, lean_uint8_sub,
    lean_uint8_to_nat, lean_uint8_to_uint32, lean_uint8_to_uint64, lean_uint32_to_uint8,
    lean_uint64_add, lean_uint64_dec_eq, lean_uint64_dec_lt, lean_uint64_land, lean_uint64_lor,
    lean_uint64_of_nat, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_nat,
    lean_uint64_to_uint8, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_instInhabited;
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_ByteArray_empty;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_IO_FS_readBinFile, l_IO_FS_writeBinFile,
    runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Internal::Parsec::ByteArray::{
    l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go,
    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg, l_Std_Internal_Parsec_ByteArray_skipBytes,
};
use crate::r#gen::Std::Internal::Parsec::{
    initialize_Std_Internal_Parsec, runtime_initialize_Std_Internal_Parsec,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Actions,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions,
};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value:
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
    m_data: [13, 10, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value:
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
    m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 39, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2: u8 = 0;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 100, 32, 119, 97, 115, 32, 48, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0: u8 = 0;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0: u8 = 0;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0: u8 = 0;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        84, 104, 101, 114, 101, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 97, 110, 121, 32,
        114, 97, 116, 72, 105, 110, 116, 115, 32, 102, 111, 114, 32, 97, 100, 100, 105, 110, 103,
        32, 116, 104, 101, 32, 101, 109, 112, 116, 121, 32, 99, 108, 97, 117, 115, 101, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 97, 116, 105, 115, 102, 105, 101, 100, 0]};
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2: u8 = 0;
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3: u8 = 0;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 122, 101, 114, 111, 32, 98, 121, 116, 101, 32, 105, 110, 32, 108, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [69, 120, 99, 101, 115, 115, 105, 118, 101, 32, 108, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value:
    leanh::LeanStringObject<52> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        112, 97, 114, 115, 101, 100, 32, 110, 111, 110, 32, 110, 101, 103, 97, 116, 105, 118, 101,
        32, 108, 105, 116, 32, 119, 104, 101, 114, 101, 32, 110, 101, 103, 97, 116, 105, 118, 101,
        32, 119, 97, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value:
    leanh::LeanStringObject<52> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        112, 97, 114, 115, 101, 100, 32, 110, 111, 110, 32, 112, 111, 115, 105, 116, 105, 118, 101,
        32, 108, 105, 116, 32, 119, 104, 101, 114, 101, 32, 112, 111, 115, 105, 116, 105, 118, 101,
        32, 119, 97, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 111, 114, 32, 100, 32, 103, 111, 116, 58,
        32, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105, 110, 112,
        117, 116, 0,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 48, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [48, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [49, 32, 100, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value: leanh::LeanStringObject<93> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 80, 97, 114, 115, 101, 114, 46, 48, 46, 83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 108, 114, 97, 116, 80, 114, 111, 111, 102, 84, 111, 66, 105, 110, 97, 114, 121, 46, 97, 100, 100, 73, 110, 116, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value: leanh::LeanStringObject<94> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 91, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 109, 97, 112, 112, 101, 100, 32, 226, 137, 164, 32, 40, 50, 94, 54, 52, 32, 45, 32, 49, 41, 32, 45, 45, 32, 111, 117, 114, 32, 112, 97, 114, 115, 101, 114, 32, 34, 111, 110, 108, 121, 34, 32, 115, 117, 112, 112, 111, 114, 116, 115, 32, 54, 52, 32, 98, 105, 116, 32, 108, 105, 116, 101, 114, 97, 108, 115, 10, 32, 32, 32, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = leanh::lean_unsigned_to_nat(0);
    v___x_2708_ = lean_nat_to_int(v___x_2707_);
    return v___x_2708_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(
    mut v_clause_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivotInt_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = l_Int_instInhabited;
    v___x_2711_ = leanh::lean_unsigned_to_nat(0);
    v_pivotInt_2712_ = lean_array_get_borrowed(v___x_2710_, v_clause_2709_, v___x_2711_);
    v___x_2713_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
    v___x_2714_ = lean_int_dec_lt(v___x_2713_, v_pivotInt_2712_);
    v___x_2715_ = lean_nat_abs(v_pivotInt_2712_);
    v___x_2716_ = leanh::lean_box((v___x_2714_) as usize);
    v___x_2717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2717_, 0, v___x_2715_);
    leanh::lean_ctor_set(v___x_2717_, 1, v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(
    mut v_clause_2718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ =
        l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(
            v_clause_2718_,
        );
    leanh::lean_dec_ref(v_clause_2718_);
    return v_res_2719_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0;
    v_utf8_2722_ = lean_string_to_utf8(v___x_2721_);
    return v_utf8_2722_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2() -> u8 {
    let mut v___x_2723_: u32 = 0;
    let mut v___x_2724_: u8 = 0;
    v___x_2723_ = 10;
    v___x_2724_ = lean_uint32_to_uint8(v___x_2723_);
    return v___x_2724_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2,
    );
    v___x_2727_ = lean_uint8_to_nat(v___x_2726_);
    return v___x_2727_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4,
    );
    v___x_2729_ = l_Nat_reprFast(v___x_2728_);
    return v___x_2729_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5,
    );
    v___x_2731_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_2732_ = lean_string_append(v___x_2731_, v___x_2730_);
    return v___x_2732_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_2735_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6,
    );
    v___x_2736_ = lean_string_append(v___x_2735_, v___x_2734_);
    return v___x_2736_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8,
    );
    v___x_2738_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2738_, 0, v___x_2737_);
    return v___x_2738_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(
    mut v_a_2739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v_utf8_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v_unused_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v_got_2764_: u8 = 0;
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2770_: u8 = 0;
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_unused_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2740_ = leanh::lean_ctor_get(v_a_2739_, 0);
                v_idx_2741_ = leanh::lean_ctor_get(v_a_2739_, 1);
                leanh::lean_inc(v_idx_2741_);
                v___x_2759_ = lean_byte_array_size(v_array_2740_);
                v___x_2760_ = lean_nat_dec_lt(v_idx_2741_, v___x_2759_);
                if v___x_2760_ == 0 {
                    v___x_2761_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_a_2739_);
                    v___x_2762_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2762_, 0, v_a_2739_);
                    leanh::lean_ctor_set(v___x_2762_, 1, v___x_2761_);
                    leanh::lean_inc(v_idx_2741_);
                    v___y_2743_ = v___x_2762_;
                    v_pos_2744_ = v_a_2739_;
                    v_idx_2745_ = v_idx_2741_;
                    state = 1;
                    continue;
                } else {
                    v___x_2763_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2,
                    );
                    v_got_2764_ = lean_byte_array_fget(v_array_2740_, v_idx_2741_);
                    v___x_2765_ = lean_uint8_dec_eq(v_got_2764_, v___x_2763_);
                    if v___x_2765_ == 0 {
                        v___x_2766_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9,
                        );
                        leanh::lean_inc_ref(v_a_2739_);
                        v___x_2767_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2767_, 0, v_a_2739_);
                        leanh::lean_ctor_set(v___x_2767_, 1, v___x_2766_);
                        leanh::lean_inc(v_idx_2741_);
                        v___y_2743_ = v___x_2767_;
                        v_pos_2744_ = v_a_2739_;
                        v_idx_2745_ = v_idx_2741_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_array_2740_);
                        v_isSharedCheck_2778_ = (!leanh::lean_is_exclusive(v_a_2739_)) as u8;
                        if v_isSharedCheck_2778_ == 0 {
                            v_unused_2779_ = leanh::lean_ctor_get(v_a_2739_, 1);
                            leanh::lean_dec(v_unused_2779_);
                            v_unused_2780_ = leanh::lean_ctor_get(v_a_2739_, 0);
                            leanh::lean_dec(v_unused_2780_);
                            v___x_2769_ = v_a_2739_;
                            v_isShared_2770_ = v_isSharedCheck_2778_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2739_);
                            v___x_2769_ = leanh::lean_box(0);
                            v_isShared_2770_ = v_isSharedCheck_2778_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2746_ = lean_nat_dec_eq(v_idx_2741_, v_idx_2745_);
                leanh::lean_dec(v_idx_2745_);
                leanh::lean_dec(v_idx_2741_);
                if v___x_2746_ == 0 {
                    leanh::lean_dec_ref(v_pos_2744_);
                    return v___y_2743_;
                } else {
                    leanh::lean_dec_ref(v___y_2743_);
                    v_utf8_2747_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1,
                    );
                    v___x_2748_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_2747_, v_pos_2744_);
                    if leanh::lean_obj_tag(v___x_2748_) == 0 {
                        v_pos_2749_ = leanh::lean_ctor_get(v___x_2748_, 0);
                        v_isSharedCheck_2757_ =
                            (!leanh::lean_is_exclusive(v___x_2748_)) as u8;
                        if v_isSharedCheck_2757_ == 0 {
                            v_unused_2758_ = leanh::lean_ctor_get(v___x_2748_, 1);
                            leanh::lean_dec(v_unused_2758_);
                            v___x_2751_ = v___x_2748_;
                            v_isShared_2752_ = v_isSharedCheck_2757_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_2749_);
                            leanh::lean_dec(v___x_2748_);
                            v___x_2751_ = leanh::lean_box(0);
                            v_isShared_2752_ = v_isSharedCheck_2757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_2748_;
                    }
                }
            }
            2 => {
                v___x_2753_ = leanh::lean_box(0);
                if v_isShared_2752_ == 0 {
                    leanh::lean_ctor_set(v___x_2751_, 1, v___x_2753_);
                    v___x_2755_ = v___x_2751_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_pos_2749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2753_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2755_;
            }
            4 => {
                v___x_2771_ = leanh::lean_unsigned_to_nat(1);
                v___x_2772_ = lean_nat_add(v_idx_2741_, v___x_2771_);
                leanh::lean_dec(v_idx_2741_);
                if v_isShared_2770_ == 0 {
                    leanh::lean_ctor_set(v___x_2769_, 1, v___x_2772_);
                    v___x_2774_ = v___x_2769_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_array_2740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2772_);
                    v___x_2774_ = v_reuseFailAlloc_2777_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2775_ = leanh::lean_box(0);
                v___x_2776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2776_, 0, v___x_2774_);
                leanh::lean_ctor_set(v___x_2776_, 1, v___x_2775_);
                return v___x_2776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2() -> u8 {
    let mut v___x_2784_: u32 = 0;
    let mut v___x_2785_: u8 = 0;
    v___x_2784_ = 48;
    v___x_2785_ = lean_uint32_to_uint8(v___x_2784_);
    return v___x_2785_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3() -> u8 {
    let mut v___x_2786_: u32 = 0;
    let mut v___x_2787_: u8 = 0;
    v___x_2786_ = 57;
    v___x_2787_ = lean_uint32_to_uint8(v___x_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(
    mut v_a_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2801_: u8 = 0;
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u32 = 0;
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_reuseFailAlloc_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2834_: u8 = 0;
    let mut v_unused_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2795_ = leanh::lean_ctor_get(v_a_2791_, 0);
                v_idx_2796_ = leanh::lean_ctor_get(v_a_2791_, 1);
                v___x_2797_ = lean_byte_array_size(v_array_2795_);
                v___x_2798_ = lean_nat_dec_lt(v_idx_2796_, v___x_2797_);
                if v___x_2798_ == 0 {
                    v___x_2799_ = leanh::lean_box(0);
                    v___x_2800_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2800_, 0, v_a_2791_);
                    leanh::lean_ctor_set(v___x_2800_, 1, v___x_2799_);
                    return v___x_2800_;
                } else {
                    v_c_2801_ = lean_byte_array_fget(v_array_2795_, v_idx_2796_);
                    v___x_2802_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_2803_ = lean_uint8_dec_le(v___x_2802_, v_c_2801_);
                    if v___x_2803_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2804_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_2805_ = lean_uint8_dec_le(v_c_2801_, v___x_2804_);
                        if v___x_2805_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_idx_2796_);
                            leanh::lean_inc_ref(v_array_2795_);
                            v_isSharedCheck_2834_ =
                                (!leanh::lean_is_exclusive(v_a_2791_)) as u8;
                            if v_isSharedCheck_2834_ == 0 {
                                v_unused_2835_ = leanh::lean_ctor_get(v_a_2791_, 1);
                                leanh::lean_dec(v_unused_2835_);
                                v_unused_2836_ = leanh::lean_ctor_get(v_a_2791_, 0);
                                leanh::lean_dec(v_unused_2836_);
                                v___x_2807_ = v_a_2791_;
                                v_isShared_2808_ = v_isSharedCheck_2834_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_2791_);
                                v___x_2807_ = leanh::lean_box(0);
                                v_isShared_2808_ = v_isSharedCheck_2834_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2793_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_2794_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2794_, 0, v_a_2791_);
                leanh::lean_ctor_set(v___x_2794_, 1, v___x_2793_);
                return v___x_2794_;
            }
            2 => {
                v___x_2809_ = leanh::lean_unsigned_to_nat(1);
                v___x_2810_ = lean_nat_add(v_idx_2796_, v___x_2809_);
                leanh::lean_dec(v_idx_2796_);
                if v_isShared_2808_ == 0 {
                    leanh::lean_ctor_set(v___x_2807_, 1, v___x_2810_);
                    v_it_x27_2812_ = v___x_2807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_array_2795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2810_);
                    v_it_x27_2812_ = v_reuseFailAlloc_2833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2813_ = lean_uint8_to_uint32(v_c_2801_);
                v___x_2814_ = lean_uint32_to_uint8(v___x_2813_);
                v___x_2815_ = lean_uint8_sub(v___x_2814_, v___x_2802_);
                v___x_2816_ = lean_uint8_to_nat(v___x_2815_);
                v___x_2817_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_2812_, v___x_2816_);
                v_fst_2818_ = leanh::lean_ctor_get(v___x_2817_, 0);
                v_snd_2819_ = leanh::lean_ctor_get(v___x_2817_, 1);
                v_isSharedCheck_2832_ = (!leanh::lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2832_ == 0 {
                    v___x_2821_ = v___x_2817_;
                    v_isShared_2822_ = v_isSharedCheck_2832_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2819_);
                    leanh::lean_inc(v_fst_2818_);
                    leanh::lean_dec(v___x_2817_);
                    v___x_2821_ = leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2823_ = leanh::lean_unsigned_to_nat(0);
                v___x_2824_ = lean_nat_dec_eq(v_fst_2818_, v___x_2823_);
                if v___x_2824_ == 0 {
                    if v_isShared_2822_ == 0 {
                        leanh::lean_ctor_set(v___x_2821_, 1, v_fst_2818_);
                        leanh::lean_ctor_set(v___x_2821_, 0, v_snd_2819_);
                        v___x_2826_ = v___x_2821_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_snd_2819_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_fst_2818_);
                        v___x_2826_ = v_reuseFailAlloc_2827_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2818_);
                    v___x_2828_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_2822_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2821_, 1);
                        leanh::lean_ctor_set(v___x_2821_, 1, v___x_2828_);
                        leanh::lean_ctor_set(v___x_2821_, 0, v_snd_2819_);
                        v___x_2830_ = v___x_2821_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2831_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_snd_2819_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2828_);
                        v___x_2830_ = v_reuseFailAlloc_2831_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2826_;
            }
            6 => {
                return v___x_2830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0() -> u8 {
    let mut v___x_2837_: u32 = 0;
    let mut v___x_2838_: u8 = 0;
    v___x_2837_ = 45;
    v___x_2838_ = lean_uint32_to_uint8(v___x_2837_);
    return v___x_2838_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2839_: u8 = 0;
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2839_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
    );
    v___x_2840_ = lean_uint8_to_nat(v___x_2839_);
    return v___x_2840_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1,
    );
    v___x_2842_ = l_Nat_reprFast(v___x_2841_);
    return v___x_2842_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2843_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2,
    );
    v___x_2844_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_2845_ = lean_string_append(v___x_2844_, v___x_2843_);
    return v___x_2845_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2846_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_2847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3,
    );
    v___x_2848_ = lean_string_append(v___x_2847_, v___x_2846_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2849_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4,
    );
    v___x_2850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2850_, 0, v___x_2849_);
    return v___x_2850_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(
    mut v_a_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v_got_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2876_: u8 = 0;
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: u8 = 0;
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: u32 = 0;
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: u8 = 0;
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2892_: u8 = 0;
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_reuseFailAlloc_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_unused_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2852_ = leanh::lean_ctor_get(v_a_2851_, 0);
                v_idx_2853_ = leanh::lean_ctor_get(v_a_2851_, 1);
                v___x_2854_ = lean_byte_array_size(v_array_2852_);
                v___x_2855_ = lean_nat_dec_lt(v_idx_2853_, v___x_2854_);
                if v___x_2855_ == 0 {
                    v___x_2856_ = leanh::lean_box(0);
                    v___x_2857_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2857_, 0, v_a_2851_);
                    leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                    return v___x_2857_;
                } else {
                    v___x_2858_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
                    );
                    v_got_2859_ = lean_byte_array_fget(v_array_2852_, v_idx_2853_);
                    v___x_2860_ = lean_uint8_dec_eq(v_got_2859_, v___x_2858_);
                    if v___x_2860_ == 0 {
                        v___x_2861_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5,
                        );
                        v___x_2862_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2862_, 0, v_a_2851_);
                        leanh::lean_ctor_set(v___x_2862_, 1, v___x_2861_);
                        return v___x_2862_;
                    } else {
                        leanh::lean_inc(v_idx_2853_);
                        leanh::lean_inc_ref(v_array_2852_);
                        v_isSharedCheck_2906_ = (!leanh::lean_is_exclusive(v_a_2851_)) as u8;
                        if v_isSharedCheck_2906_ == 0 {
                            v_unused_2907_ = leanh::lean_ctor_get(v_a_2851_, 1);
                            leanh::lean_dec(v_unused_2907_);
                            v_unused_2908_ = leanh::lean_ctor_get(v_a_2851_, 0);
                            leanh::lean_dec(v_unused_2908_);
                            v___x_2864_ = v_a_2851_;
                            v_isShared_2865_ = v_isSharedCheck_2906_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2851_);
                            v___x_2864_ = leanh::lean_box(0);
                            v_isShared_2865_ = v_isSharedCheck_2906_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2866_ = leanh::lean_unsigned_to_nat(1);
                v___x_2867_ = lean_nat_add(v_idx_2853_, v___x_2866_);
                leanh::lean_dec(v_idx_2853_);
                leanh::lean_inc(v___x_2867_);
                leanh::lean_inc_ref(v_array_2852_);
                if v_isShared_2865_ == 0 {
                    leanh::lean_ctor_set(v___x_2864_, 1, v___x_2867_);
                    v___x_2869_ = v___x_2864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_array_2852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___x_2867_);
                    v___x_2869_ = v_reuseFailAlloc_2905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2873_ = lean_nat_dec_lt(v___x_2867_, v___x_2854_);
                if v___x_2873_ == 0 {
                    leanh::lean_dec(v___x_2867_);
                    leanh::lean_dec_ref(v_array_2852_);
                    v___x_2874_ = leanh::lean_box(0);
                    v___x_2875_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2875_, 0, v___x_2869_);
                    leanh::lean_ctor_set(v___x_2875_, 1, v___x_2874_);
                    return v___x_2875_;
                } else {
                    v_c_2876_ = lean_byte_array_fget(v_array_2852_, v___x_2867_);
                    v___x_2877_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_2878_ = lean_uint8_dec_le(v___x_2877_, v_c_2876_);
                    if v___x_2878_ == 0 {
                        leanh::lean_dec(v___x_2867_);
                        leanh::lean_dec_ref(v_array_2852_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2879_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_2880_ = lean_uint8_dec_le(v_c_2876_, v___x_2879_);
                        if v___x_2880_ == 0 {
                            leanh::lean_dec(v___x_2867_);
                            leanh::lean_dec_ref(v_array_2852_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_2869_);
                            v___x_2881_ = lean_nat_add(v___x_2867_, v___x_2866_);
                            leanh::lean_dec(v___x_2867_);
                            v_it_x27_2882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_it_x27_2882_, 0, v_array_2852_);
                            leanh::lean_ctor_set(v_it_x27_2882_, 1, v___x_2881_);
                            v___x_2883_ = lean_uint8_to_uint32(v_c_2876_);
                            v___x_2884_ = lean_uint32_to_uint8(v___x_2883_);
                            v___x_2885_ = lean_uint8_sub(v___x_2884_, v___x_2877_);
                            v___x_2886_ = lean_uint8_to_nat(v___x_2885_);
                            v___x_2887_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_2882_, v___x_2886_);
                            v_fst_2888_ = leanh::lean_ctor_get(v___x_2887_, 0);
                            v_snd_2889_ = leanh::lean_ctor_get(v___x_2887_, 1);
                            v_isSharedCheck_2904_ =
                                (!leanh::lean_is_exclusive(v___x_2887_)) as u8;
                            if v_isSharedCheck_2904_ == 0 {
                                v___x_2891_ = v___x_2887_;
                                v_isShared_2892_ = v_isSharedCheck_2904_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_2889_);
                                leanh::lean_inc(v_fst_2888_);
                                leanh::lean_dec(v___x_2887_);
                                v___x_2891_ = leanh::lean_box(0);
                                v_isShared_2892_ = v_isSharedCheck_2904_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2871_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_2872_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2872_, 0, v___x_2869_);
                leanh::lean_ctor_set(v___x_2872_, 1, v___x_2871_);
                return v___x_2872_;
            }
            4 => {
                v___x_2893_ = leanh::lean_unsigned_to_nat(0);
                v___x_2894_ = lean_nat_dec_eq(v_fst_2888_, v___x_2893_);
                if v___x_2894_ == 0 {
                    v___x_2895_ = lean_nat_to_int(v_fst_2888_);
                    v___x_2896_ = lean_int_neg(v___x_2895_);
                    leanh::lean_dec(v___x_2895_);
                    if v_isShared_2892_ == 0 {
                        leanh::lean_ctor_set(v___x_2891_, 1, v___x_2896_);
                        leanh::lean_ctor_set(v___x_2891_, 0, v_snd_2889_);
                        v___x_2898_ = v___x_2891_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_snd_2889_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2896_);
                        v___x_2898_ = v_reuseFailAlloc_2899_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2888_);
                    v___x_2900_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_2892_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2891_, 1);
                        leanh::lean_ctor_set(v___x_2891_, 1, v___x_2900_);
                        leanh::lean_ctor_set(v___x_2891_, 0, v_snd_2889_);
                        v___x_2902_ = v___x_2891_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2903_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_snd_2889_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2900_);
                        v___x_2902_ = v_reuseFailAlloc_2903_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2898_;
            }
            6 => {
                return v___x_2902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(
    mut v_a_2909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2919_: u8 = 0;
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u32 = 0;
    let mut v___x_2932_: u8 = 0;
    let mut v___x_2933_: u8 = 0;
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_reuseFailAlloc_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_unused_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2913_ = leanh::lean_ctor_get(v_a_2909_, 0);
                v_idx_2914_ = leanh::lean_ctor_get(v_a_2909_, 1);
                v___x_2915_ = lean_byte_array_size(v_array_2913_);
                v___x_2916_ = lean_nat_dec_lt(v_idx_2914_, v___x_2915_);
                if v___x_2916_ == 0 {
                    v___x_2917_ = leanh::lean_box(0);
                    v___x_2918_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2918_, 0, v_a_2909_);
                    leanh::lean_ctor_set(v___x_2918_, 1, v___x_2917_);
                    return v___x_2918_;
                } else {
                    v_c_2919_ = lean_byte_array_fget(v_array_2913_, v_idx_2914_);
                    v___x_2920_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_2921_ = lean_uint8_dec_le(v___x_2920_, v_c_2919_);
                    if v___x_2921_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2922_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_2923_ = lean_uint8_dec_le(v_c_2919_, v___x_2922_);
                        if v___x_2923_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_idx_2914_);
                            leanh::lean_inc_ref(v_array_2913_);
                            v_isSharedCheck_2952_ =
                                (!leanh::lean_is_exclusive(v_a_2909_)) as u8;
                            if v_isSharedCheck_2952_ == 0 {
                                v_unused_2953_ = leanh::lean_ctor_get(v_a_2909_, 1);
                                leanh::lean_dec(v_unused_2953_);
                                v_unused_2954_ = leanh::lean_ctor_get(v_a_2909_, 0);
                                leanh::lean_dec(v_unused_2954_);
                                v___x_2925_ = v_a_2909_;
                                v_isShared_2926_ = v_isSharedCheck_2952_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_2909_);
                                v___x_2925_ = leanh::lean_box(0);
                                v_isShared_2926_ = v_isSharedCheck_2952_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2911_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_2912_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2912_, 0, v_a_2909_);
                leanh::lean_ctor_set(v___x_2912_, 1, v___x_2911_);
                return v___x_2912_;
            }
            2 => {
                v___x_2927_ = leanh::lean_unsigned_to_nat(1);
                v___x_2928_ = lean_nat_add(v_idx_2914_, v___x_2927_);
                leanh::lean_dec(v_idx_2914_);
                if v_isShared_2926_ == 0 {
                    leanh::lean_ctor_set(v___x_2925_, 1, v___x_2928_);
                    v_it_x27_2930_ = v___x_2925_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_array_2913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2928_);
                    v_it_x27_2930_ = v_reuseFailAlloc_2951_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2931_ = lean_uint8_to_uint32(v_c_2919_);
                v___x_2932_ = lean_uint32_to_uint8(v___x_2931_);
                v___x_2933_ = lean_uint8_sub(v___x_2932_, v___x_2920_);
                v___x_2934_ = lean_uint8_to_nat(v___x_2933_);
                v___x_2935_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_2930_, v___x_2934_);
                v_fst_2936_ = leanh::lean_ctor_get(v___x_2935_, 0);
                v_snd_2937_ = leanh::lean_ctor_get(v___x_2935_, 1);
                v_isSharedCheck_2950_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                if v_isSharedCheck_2950_ == 0 {
                    v___x_2939_ = v___x_2935_;
                    v_isShared_2940_ = v_isSharedCheck_2950_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2937_);
                    leanh::lean_inc(v_fst_2936_);
                    leanh::lean_dec(v___x_2935_);
                    v___x_2939_ = leanh::lean_box(0);
                    v_isShared_2940_ = v_isSharedCheck_2950_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2941_ = leanh::lean_unsigned_to_nat(0);
                v___x_2942_ = lean_nat_dec_eq(v_fst_2936_, v___x_2941_);
                if v___x_2942_ == 0 {
                    if v_isShared_2940_ == 0 {
                        leanh::lean_ctor_set(v___x_2939_, 1, v_fst_2936_);
                        leanh::lean_ctor_set(v___x_2939_, 0, v_snd_2937_);
                        v___x_2944_ = v___x_2939_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2945_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_snd_2937_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_fst_2936_);
                        v___x_2944_ = v_reuseFailAlloc_2945_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2936_);
                    v___x_2946_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_2940_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2939_, 1);
                        leanh::lean_ctor_set(v___x_2939_, 1, v___x_2946_);
                        leanh::lean_ctor_set(v___x_2939_, 0, v_snd_2937_);
                        v___x_2948_ = v___x_2939_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2949_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_snd_2937_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 1, v___x_2946_);
                        v___x_2948_ = v_reuseFailAlloc_2949_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2944_;
            }
            6 => {
                return v___x_2948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2955_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
    );
    v___x_2956_ = lean_uint8_to_nat(v___x_2955_);
    return v___x_2956_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0,
    );
    v___x_2958_ = l_Nat_reprFast(v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1,
    );
    v___x_2960_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_2961_ = lean_string_append(v___x_2960_, v___x_2959_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_2963_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2,
    );
    v___x_2964_ = lean_string_append(v___x_2963_, v___x_2962_);
    return v___x_2964_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3,
    );
    v___x_2966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2966_, 0, v___x_2965_);
    return v___x_2966_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(
    mut v_a_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut v_got_2975_: u8 = 0;
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_unused_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2968_ = leanh::lean_ctor_get(v_a_2967_, 0);
                v_idx_2969_ = leanh::lean_ctor_get(v_a_2967_, 1);
                v___x_2970_ = lean_byte_array_size(v_array_2968_);
                v___x_2971_ = lean_nat_dec_lt(v_idx_2969_, v___x_2970_);
                if v___x_2971_ == 0 {
                    v___x_2972_ = leanh::lean_box(0);
                    v___x_2973_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2973_, 0, v_a_2967_);
                    leanh::lean_ctor_set(v___x_2973_, 1, v___x_2972_);
                    return v___x_2973_;
                } else {
                    v___x_2974_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v_got_2975_ = lean_byte_array_fget(v_array_2968_, v_idx_2969_);
                    v___x_2976_ = lean_uint8_dec_eq(v_got_2975_, v___x_2974_);
                    if v___x_2976_ == 0 {
                        v___x_2977_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        v___x_2978_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2978_, 0, v_a_2967_);
                        leanh::lean_ctor_set(v___x_2978_, 1, v___x_2977_);
                        return v___x_2978_;
                    } else {
                        leanh::lean_inc(v_idx_2969_);
                        leanh::lean_inc_ref(v_array_2968_);
                        v_isSharedCheck_2989_ = (!leanh::lean_is_exclusive(v_a_2967_)) as u8;
                        if v_isSharedCheck_2989_ == 0 {
                            v_unused_2990_ = leanh::lean_ctor_get(v_a_2967_, 1);
                            leanh::lean_dec(v_unused_2990_);
                            v_unused_2991_ = leanh::lean_ctor_get(v_a_2967_, 0);
                            leanh::lean_dec(v_unused_2991_);
                            v___x_2980_ = v_a_2967_;
                            v_isShared_2981_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2967_);
                            v___x_2980_ = leanh::lean_box(0);
                            v_isShared_2981_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2982_ = leanh::lean_unsigned_to_nat(1);
                v___x_2983_ = lean_nat_add(v_idx_2969_, v___x_2982_);
                leanh::lean_dec(v_idx_2969_);
                if v_isShared_2981_ == 0 {
                    leanh::lean_ctor_set(v___x_2980_, 1, v___x_2983_);
                    v___x_2985_ = v___x_2980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_array_2968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2983_);
                    v___x_2985_ = v_reuseFailAlloc_2988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2986_ = leanh::lean_box(0);
                v___x_2987_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2987_, 0, v___x_2985_);
                leanh::lean_ctor_set(v___x_2987_, 1, v___x_2986_);
                return v___x_2987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0()
-> u8 {
    let mut v___x_2992_: u32 = 0;
    let mut v___x_2993_: u8 = 0;
    v___x_2992_ = 32;
    v___x_2993_ = lean_uint32_to_uint8(v___x_2992_);
    return v___x_2993_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2994_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
    v___x_2995_ = lean_uint8_to_nat(v___x_2994_);
    return v___x_2995_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2996_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1);
    v___x_2997_ = l_Nat_reprFast(v___x_2996_);
    return v___x_2997_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2);
    v___x_2999_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_3000_ = lean_string_append(v___x_2999_, v___x_2998_);
    return v___x_3000_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3001_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_3002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3);
    v___x_3003_ = lean_string_append(v___x_3002_, v___x_3001_);
    return v___x_3003_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3004_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4);
    v___x_3005_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3005_, 0, v___x_3004_);
    return v___x_3005_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(
    mut v_a_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: u8 = 0;
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u32 = 0;
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: u8 = 0;
    let mut v_array_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    let mut v_got_3045_: u8 = 0;
    let mut v___x_3046_: u8 = 0;
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_unused_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3010_ = leanh::lean_ctor_get(v_a_3006_, 0);
                v_idx_3011_ = leanh::lean_ctor_get(v_a_3006_, 1);
                v___x_3012_ = lean_byte_array_size(v_array_3010_);
                v___x_3013_ = lean_nat_dec_lt(v_idx_3011_, v___x_3012_);
                if v___x_3013_ == 0 {
                    v___x_3014_ = leanh::lean_box(0);
                    v___x_3015_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3015_, 0, v_a_3006_);
                    leanh::lean_ctor_set(v___x_3015_, 1, v___x_3014_);
                    return v___x_3015_;
                } else {
                    v_c_3016_ = lean_byte_array_fget(v_array_3010_, v_idx_3011_);
                    v___x_3017_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_3018_ = lean_uint8_dec_le(v___x_3017_, v_c_3016_);
                    if v___x_3018_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3019_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_3020_ = lean_uint8_dec_le(v_c_3016_, v___x_3019_);
                        if v___x_3020_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3021_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3022_ = lean_nat_add(v_idx_3011_, v___x_3021_);
                            leanh::lean_inc_ref(v_array_3010_);
                            v_it_x27_3023_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_it_x27_3023_, 0, v_array_3010_);
                            leanh::lean_ctor_set(v_it_x27_3023_, 1, v___x_3022_);
                            v___x_3024_ = lean_uint8_to_uint32(v_c_3016_);
                            v___x_3025_ = lean_uint32_to_uint8(v___x_3024_);
                            v___x_3026_ = lean_uint8_sub(v___x_3025_, v___x_3017_);
                            v___x_3027_ = lean_uint8_to_nat(v___x_3026_);
                            v___x_3028_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3023_, v___x_3027_);
                            v_fst_3029_ = leanh::lean_ctor_get(v___x_3028_, 0);
                            v_snd_3030_ = leanh::lean_ctor_get(v___x_3028_, 1);
                            v_isSharedCheck_3068_ =
                                (!leanh::lean_is_exclusive(v___x_3028_)) as u8;
                            if v_isSharedCheck_3068_ == 0 {
                                v___x_3032_ = v___x_3028_;
                                v_isShared_3033_ = v_isSharedCheck_3068_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_3030_);
                                leanh::lean_inc(v_fst_3029_);
                                leanh::lean_dec(v___x_3028_);
                                v___x_3032_ = leanh::lean_box(0);
                                v_isShared_3033_ = v_isSharedCheck_3068_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3008_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3009_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3009_, 0, v_a_3006_);
                leanh::lean_ctor_set(v___x_3009_, 1, v___x_3008_);
                return v___x_3009_;
            }
            2 => {
                v___x_3034_ = leanh::lean_unsigned_to_nat(0);
                v___x_3035_ = lean_nat_dec_eq(v_fst_3029_, v___x_3034_);
                if v___x_3035_ == 0 {
                    leanh::lean_dec_ref(v_a_3006_);
                    v_array_3036_ = leanh::lean_ctor_get(v_snd_3030_, 0);
                    v_idx_3037_ = leanh::lean_ctor_get(v_snd_3030_, 1);
                    v___x_3038_ = lean_byte_array_size(v_array_3036_);
                    v___x_3039_ = lean_nat_dec_lt(v_idx_3037_, v___x_3038_);
                    if v___x_3039_ == 0 {
                        leanh::lean_dec(v_fst_3029_);
                        v___x_3040_ = leanh::lean_box(0);
                        if v_isShared_3033_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3032_, 1);
                            leanh::lean_ctor_set(v___x_3032_, 1, v___x_3040_);
                            leanh::lean_ctor_set(v___x_3032_, 0, v_snd_3030_);
                            v___x_3042_ = v___x_3032_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3043_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_snd_3030_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3040_);
                            v___x_3042_ = v_reuseFailAlloc_3043_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3044_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                        v_got_3045_ = lean_byte_array_fget(v_array_3036_, v_idx_3037_);
                        v___x_3046_ = lean_uint8_dec_eq(v_got_3045_, v___x_3044_);
                        if v___x_3046_ == 0 {
                            leanh::lean_dec(v_fst_3029_);
                            v___x_3047_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                            if v_isShared_3033_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3032_, 1);
                                leanh::lean_ctor_set(v___x_3032_, 1, v___x_3047_);
                                leanh::lean_ctor_set(v___x_3032_, 0, v_snd_3030_);
                                v___x_3049_ = v___x_3032_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3050_ =
                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_snd_3030_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3047_);
                                v___x_3049_ = v_reuseFailAlloc_3050_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v_idx_3037_);
                            leanh::lean_inc_ref(v_array_3036_);
                            v_isSharedCheck_3061_ =
                                (!leanh::lean_is_exclusive(v_snd_3030_)) as u8;
                            if v_isSharedCheck_3061_ == 0 {
                                v_unused_3062_ = leanh::lean_ctor_get(v_snd_3030_, 1);
                                leanh::lean_dec(v_unused_3062_);
                                v_unused_3063_ = leanh::lean_ctor_get(v_snd_3030_, 0);
                                leanh::lean_dec(v_unused_3063_);
                                v___x_3052_ = v_snd_3030_;
                                v_isShared_3053_ = v_isSharedCheck_3061_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v_snd_3030_);
                                v___x_3052_ = leanh::lean_box(0);
                                v_isShared_3053_ = v_isSharedCheck_3061_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_3030_);
                    leanh::lean_dec(v_fst_3029_);
                    v___x_3064_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3033_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3032_, 1);
                        leanh::lean_ctor_set(v___x_3032_, 1, v___x_3064_);
                        leanh::lean_ctor_set(v___x_3032_, 0, v_a_3006_);
                        v___x_3066_ = v___x_3032_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3067_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3006_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3064_);
                        v___x_3066_ = v_reuseFailAlloc_3067_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3042_;
            }
            4 => {
                return v___x_3049_;
            }
            5 => {
                v___x_3054_ = lean_nat_add(v_idx_3037_, v___x_3021_);
                leanh::lean_dec(v_idx_3037_);
                if v_isShared_3053_ == 0 {
                    leanh::lean_ctor_set(v___x_3052_, 1, v___x_3054_);
                    v___x_3056_ = v___x_3052_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_array_3036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3054_);
                    v___x_3056_ = v_reuseFailAlloc_3060_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3033_ == 0 {
                    leanh::lean_ctor_set(v___x_3032_, 1, v_fst_3029_);
                    leanh::lean_ctor_set(v___x_3032_, 0, v___x_3056_);
                    v___x_3058_ = v___x_3032_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_fst_3029_);
                    v___x_3058_ = v_reuseFailAlloc_3059_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3058_;
            }
            8 => {
                return v___x_3066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(
    mut v_acc_3069_: *mut leanh::LeanObject,
    mut v_a_3070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3085_: u8 = 0;
    let mut v___x_3086_: u8 = 0;
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: u8 = 0;
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u32 = 0;
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v_array_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v_got_3108_: u8 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3113_: u8 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v_unused_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3071_ = leanh::lean_ctor_get(v_a_3070_, 0);
                v_idx_3072_ = leanh::lean_ctor_get(v_a_3070_, 1);
                leanh::lean_inc(v_idx_3072_);
                v___x_3082_ = lean_byte_array_size(v_array_3071_);
                v___x_3083_ = lean_nat_dec_lt(v_idx_3072_, v___x_3082_);
                if v___x_3083_ == 0 {
                    v___x_3084_ = leanh::lean_box(0);
                    leanh::lean_inc(v_idx_3072_);
                    v_pos_3074_ = v_a_3070_;
                    v_idx_3075_ = v_idx_3072_;
                    v_err_3076_ = v___x_3084_;
                    state = 1;
                    continue;
                } else {
                    v_c_3085_ = lean_byte_array_fget(v_array_3071_, v_idx_3072_);
                    v___x_3086_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_3087_ = lean_uint8_dec_le(v___x_3086_, v_c_3085_);
                    if v___x_3087_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_3088_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_3089_ = lean_uint8_dec_le(v_c_3085_, v___x_3088_);
                        if v___x_3089_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_3090_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3091_ = lean_nat_add(v_idx_3072_, v___x_3090_);
                            leanh::lean_inc_ref(v_array_3071_);
                            v_it_x27_3092_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_it_x27_3092_, 0, v_array_3071_);
                            leanh::lean_ctor_set(v_it_x27_3092_, 1, v___x_3091_);
                            v___x_3093_ = lean_uint8_to_uint32(v_c_3085_);
                            v___x_3094_ = lean_uint32_to_uint8(v___x_3093_);
                            v___x_3095_ = lean_uint8_sub(v___x_3094_, v___x_3086_);
                            v___x_3096_ = lean_uint8_to_nat(v___x_3095_);
                            v___x_3097_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3092_, v___x_3096_);
                            v_fst_3098_ = leanh::lean_ctor_get(v___x_3097_, 0);
                            leanh::lean_inc(v_fst_3098_);
                            v_snd_3099_ = leanh::lean_ctor_get(v___x_3097_, 1);
                            leanh::lean_inc(v_snd_3099_);
                            leanh::lean_dec_ref(v___x_3097_);
                            v___x_3100_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3101_ = lean_nat_dec_eq(v_fst_3098_, v___x_3100_);
                            if v___x_3101_ == 0 {
                                leanh::lean_dec_ref(v_a_3070_);
                                v_array_3102_ = leanh::lean_ctor_get(v_snd_3099_, 0);
                                v_idx_3103_ = leanh::lean_ctor_get(v_snd_3099_, 1);
                                leanh::lean_inc(v_idx_3103_);
                                v___x_3104_ = lean_byte_array_size(v_array_3102_);
                                v___x_3105_ = lean_nat_dec_lt(v_idx_3103_, v___x_3104_);
                                if v___x_3105_ == 0 {
                                    leanh::lean_dec(v_fst_3098_);
                                    v___x_3106_ = leanh::lean_box(0);
                                    v_pos_3074_ = v_snd_3099_;
                                    v_idx_3075_ = v_idx_3103_;
                                    v_err_3076_ = v___x_3106_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3107_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                                    v_got_3108_ = lean_byte_array_fget(v_array_3102_, v_idx_3103_);
                                    v___x_3109_ = lean_uint8_dec_eq(v_got_3108_, v___x_3107_);
                                    if v___x_3109_ == 0 {
                                        leanh::lean_dec(v_fst_3098_);
                                        v___x_3110_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                                        v_pos_3074_ = v_snd_3099_;
                                        v_idx_3075_ = v_idx_3103_;
                                        v_err_3076_ = v___x_3110_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc_ref(v_array_3102_);
                                        leanh::lean_dec(v_idx_3072_);
                                        v_isSharedCheck_3120_ =
                                            (!leanh::lean_is_exclusive(v_snd_3099_)) as u8;
                                        if v_isSharedCheck_3120_ == 0 {
                                            v_unused_3121_ =
                                                leanh::lean_ctor_get(v_snd_3099_, 1);
                                            leanh::lean_dec(v_unused_3121_);
                                            v_unused_3122_ =
                                                leanh::lean_ctor_get(v_snd_3099_, 0);
                                            leanh::lean_dec(v_unused_3122_);
                                            v___x_3112_ = v_snd_3099_;
                                            v_isShared_3113_ = v_isSharedCheck_3120_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_snd_3099_);
                                            v___x_3112_ = leanh::lean_box(0);
                                            v_isShared_3113_ = v_isSharedCheck_3120_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_snd_3099_);
                                leanh::lean_dec(v_fst_3098_);
                                v___x_3123_ =
                                    l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                                leanh::lean_inc(v_idx_3072_);
                                v_pos_3074_ = v_a_3070_;
                                v_idx_3075_ = v_idx_3072_;
                                v_err_3076_ = v___x_3123_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3077_ = lean_nat_dec_eq(v_idx_3072_, v_idx_3075_);
                leanh::lean_dec(v_idx_3075_);
                leanh::lean_dec(v_idx_3072_);
                if v___x_3077_ == 0 {
                    leanh::lean_dec_ref(v_acc_3069_);
                    leanh::lean_inc(v_err_3076_);
                    v___x_3078_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3078_, 0, v_pos_3074_);
                    leanh::lean_ctor_set(v___x_3078_, 1, v_err_3076_);
                    return v___x_3078_;
                } else {
                    v___x_3079_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3079_, 0, v_pos_3074_);
                    leanh::lean_ctor_set(v___x_3079_, 1, v_acc_3069_);
                    return v___x_3079_;
                }
            }
            2 => {
                v___x_3081_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                leanh::lean_inc(v_idx_3072_);
                v_pos_3074_ = v_a_3070_;
                v_idx_3075_ = v_idx_3072_;
                v_err_3076_ = v___x_3081_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3114_ = lean_nat_add(v_idx_3103_, v___x_3090_);
                leanh::lean_dec(v_idx_3103_);
                if v_isShared_3113_ == 0 {
                    leanh::lean_ctor_set(v___x_3112_, 1, v___x_3114_);
                    v___x_3116_ = v___x_3112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_array_3102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3114_);
                    v___x_3116_ = v_reuseFailAlloc_3119_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3117_ = lean_array_push(v_acc_3069_, v_fst_3098_);
                v_acc_3069_ = v___x_3117_;
                v_a_3070_ = v___x_3116_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(
    mut v_a_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3127_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0;
    v___x_3128_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(v___x_3127_, v_a_3126_);
    return v___x_3128_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0() -> u8 {
    let mut v___x_3129_: u32 = 0;
    let mut v___x_3130_: u8 = 0;
    v___x_3129_ = 100;
    v___x_3130_ = lean_uint32_to_uint8(v___x_3129_);
    return v___x_3130_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0,
    );
    v___x_3132_ = lean_uint8_to_nat(v___x_3131_);
    return v___x_3132_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1,
    );
    v___x_3134_ = l_Nat_reprFast(v___x_3133_);
    return v___x_3134_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3135_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2,
    );
    v___x_3136_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_3137_ = lean_string_append(v___x_3136_, v___x_3135_);
    return v___x_3137_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_3139_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3,
    );
    v___x_3140_ = lean_string_append(v___x_3139_, v___x_3138_);
    return v___x_3140_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3141_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4,
    );
    v___x_3142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3142_, 0, v___x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(
    mut v_a_3143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: u8 = 0;
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v_got_3151_: u8 = 0;
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v_got_3166_: u8 = 0;
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v_array_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v_got_3187_: u8 = 0;
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut v_unused_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut v_pos_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut v_reuseFailAlloc_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut v_unused_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3144_ = leanh::lean_ctor_get(v_a_3143_, 0);
                v_idx_3145_ = leanh::lean_ctor_get(v_a_3143_, 1);
                v___x_3146_ = lean_byte_array_size(v_array_3144_);
                v___x_3147_ = lean_nat_dec_lt(v_idx_3145_, v___x_3146_);
                if v___x_3147_ == 0 {
                    v___x_3148_ = leanh::lean_box(0);
                    v___x_3149_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3149_, 0, v_a_3143_);
                    leanh::lean_ctor_set(v___x_3149_, 1, v___x_3148_);
                    return v___x_3149_;
                } else {
                    v___x_3150_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0,
                    );
                    v_got_3151_ = lean_byte_array_fget(v_array_3144_, v_idx_3145_);
                    v___x_3152_ = lean_uint8_dec_eq(v_got_3151_, v___x_3150_);
                    if v___x_3152_ == 0 {
                        v___x_3153_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5,
                        );
                        v___x_3154_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3154_, 0, v_a_3143_);
                        leanh::lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                        return v___x_3154_;
                    } else {
                        leanh::lean_inc(v_idx_3145_);
                        leanh::lean_inc_ref(v_array_3144_);
                        v_isSharedCheck_3218_ = (!leanh::lean_is_exclusive(v_a_3143_)) as u8;
                        if v_isSharedCheck_3218_ == 0 {
                            v_unused_3219_ = leanh::lean_ctor_get(v_a_3143_, 1);
                            leanh::lean_dec(v_unused_3219_);
                            v_unused_3220_ = leanh::lean_ctor_get(v_a_3143_, 0);
                            leanh::lean_dec(v_unused_3220_);
                            v___x_3156_ = v_a_3143_;
                            v_isShared_3157_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3143_);
                            v___x_3156_ = leanh::lean_box(0);
                            v_isShared_3157_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3158_ = leanh::lean_unsigned_to_nat(1);
                v___x_3159_ = lean_nat_add(v_idx_3145_, v___x_3158_);
                leanh::lean_dec(v_idx_3145_);
                leanh::lean_inc(v___x_3159_);
                leanh::lean_inc_ref(v_array_3144_);
                if v_isShared_3157_ == 0 {
                    leanh::lean_ctor_set(v___x_3156_, 1, v___x_3159_);
                    v___x_3161_ = v___x_3156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_array_3144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3159_);
                    v___x_3161_ = v_reuseFailAlloc_3217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3162_ = lean_nat_dec_lt(v___x_3159_, v___x_3146_);
                if v___x_3162_ == 0 {
                    leanh::lean_dec(v___x_3159_);
                    leanh::lean_dec_ref(v_array_3144_);
                    v___x_3163_ = leanh::lean_box(0);
                    v___x_3164_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3164_, 0, v___x_3161_);
                    leanh::lean_ctor_set(v___x_3164_, 1, v___x_3163_);
                    return v___x_3164_;
                } else {
                    v___x_3165_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3166_ = lean_byte_array_fget(v_array_3144_, v___x_3159_);
                    v___x_3167_ = lean_uint8_dec_eq(v_got_3166_, v___x_3165_);
                    if v___x_3167_ == 0 {
                        leanh::lean_dec(v___x_3159_);
                        leanh::lean_dec_ref(v_array_3144_);
                        v___x_3168_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        v___x_3169_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3169_, 0, v___x_3161_);
                        leanh::lean_ctor_set(v___x_3169_, 1, v___x_3168_);
                        return v___x_3169_;
                    } else {
                        leanh::lean_dec_ref(v___x_3161_);
                        v___x_3170_ = lean_nat_add(v___x_3159_, v___x_3158_);
                        leanh::lean_dec(v___x_3159_);
                        v___x_3171_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3171_, 0, v_array_3144_);
                        leanh::lean_ctor_set(v___x_3171_, 1, v___x_3170_);
                        v___x_3172_ =
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_3171_);
                        if leanh::lean_obj_tag(v___x_3172_) == 0 {
                            v_pos_3173_ = leanh::lean_ctor_get(v___x_3172_, 0);
                            v_res_3174_ = leanh::lean_ctor_get(v___x_3172_, 1);
                            v_isSharedCheck_3207_ =
                                (!leanh::lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3207_ == 0 {
                                v___x_3176_ = v___x_3172_;
                                v_isShared_3177_ = v_isSharedCheck_3207_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_res_3174_);
                                leanh::lean_inc(v_pos_3173_);
                                leanh::lean_dec(v___x_3172_);
                                v___x_3176_ = leanh::lean_box(0);
                                v_isShared_3177_ = v_isSharedCheck_3207_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_pos_3208_ = leanh::lean_ctor_get(v___x_3172_, 0);
                            v_err_3209_ = leanh::lean_ctor_get(v___x_3172_, 1);
                            v_isSharedCheck_3216_ =
                                (!leanh::lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3216_ == 0 {
                                v___x_3211_ = v___x_3172_;
                                v_isShared_3212_ = v_isSharedCheck_3216_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_3209_);
                                leanh::lean_inc(v_pos_3208_);
                                leanh::lean_dec(v___x_3172_);
                                v___x_3211_ = leanh::lean_box(0);
                                v_isShared_3212_ = v_isSharedCheck_3216_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v_array_3178_ = leanh::lean_ctor_get(v_pos_3173_, 0);
                v_idx_3179_ = leanh::lean_ctor_get(v_pos_3173_, 1);
                v___x_3180_ = lean_byte_array_size(v_array_3178_);
                v___x_3181_ = lean_nat_dec_lt(v_idx_3179_, v___x_3180_);
                if v___x_3181_ == 0 {
                    leanh::lean_dec(v_res_3174_);
                    v___x_3182_ = leanh::lean_box(0);
                    if v_isShared_3177_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3176_, 1);
                        leanh::lean_ctor_set(v___x_3176_, 1, v___x_3182_);
                        v___x_3184_ = v___x_3176_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3185_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_pos_3173_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_3182_);
                        v___x_3184_ = v_reuseFailAlloc_3185_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3186_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v_got_3187_ = lean_byte_array_fget(v_array_3178_, v_idx_3179_);
                    v___x_3188_ = lean_uint8_dec_eq(v_got_3187_, v___x_3186_);
                    if v___x_3188_ == 0 {
                        leanh::lean_dec(v_res_3174_);
                        v___x_3189_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        if v_isShared_3177_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3176_, 1);
                            leanh::lean_ctor_set(v___x_3176_, 1, v___x_3189_);
                            v___x_3191_ = v___x_3176_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3192_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_pos_3173_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3189_);
                            v___x_3191_ = v_reuseFailAlloc_3192_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_3179_);
                        leanh::lean_inc_ref(v_array_3178_);
                        v_isSharedCheck_3204_ =
                            (!leanh::lean_is_exclusive(v_pos_3173_)) as u8;
                        if v_isSharedCheck_3204_ == 0 {
                            v_unused_3205_ = leanh::lean_ctor_get(v_pos_3173_, 1);
                            leanh::lean_dec(v_unused_3205_);
                            v_unused_3206_ = leanh::lean_ctor_get(v_pos_3173_, 0);
                            leanh::lean_dec(v_unused_3206_);
                            v___x_3194_ = v_pos_3173_;
                            v_isShared_3195_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3173_);
                            v___x_3194_ = leanh::lean_box(0);
                            v_isShared_3195_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3184_;
            }
            5 => {
                return v___x_3191_;
            }
            6 => {
                v___x_3196_ = lean_nat_add(v_idx_3179_, v___x_3158_);
                leanh::lean_dec(v_idx_3179_);
                if v_isShared_3195_ == 0 {
                    leanh::lean_ctor_set(v___x_3194_, 1, v___x_3196_);
                    v___x_3198_ = v___x_3194_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_array_3178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3196_);
                    v___x_3198_ = v_reuseFailAlloc_3203_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3199_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3199_, 0, v_res_3174_);
                if v_isShared_3177_ == 0 {
                    leanh::lean_ctor_set(v___x_3176_, 1, v___x_3199_);
                    leanh::lean_ctor_set(v___x_3176_, 0, v___x_3198_);
                    v___x_3201_ = v___x_3176_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3199_);
                    v___x_3201_ = v_reuseFailAlloc_3202_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3201_;
            }
            9 => {
                if v_isShared_3212_ == 0 {
                    v___x_3214_ = v___x_3211_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3215_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_pos_3208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_err_3209_);
                    v___x_3214_ = v_reuseFailAlloc_3215_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(
    mut v_a_3221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: u8 = 0;
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3242_: u8 = 0;
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u32 = 0;
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_reuseFailAlloc_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_unused_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3289_: u8 = 0;
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u32 = 0;
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_reuseFailAlloc_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_unused_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3225_ = leanh::lean_ctor_get(v_a_3221_, 0);
                v_idx_3226_ = leanh::lean_ctor_get(v_a_3221_, 1);
                v___x_3227_ = lean_byte_array_size(v_array_3225_);
                v___x_3228_ = lean_nat_dec_lt(v_idx_3226_, v___x_3227_);
                if v___x_3228_ == 0 {
                    v___x_3229_ = leanh::lean_box(0);
                    v___x_3230_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3230_, 0, v_a_3221_);
                    leanh::lean_ctor_set(v___x_3230_, 1, v___x_3229_);
                    return v___x_3230_;
                } else {
                    v___x_3231_ = lean_byte_array_fget(v_array_3225_, v_idx_3226_);
                    v___x_3232_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
                    );
                    v___x_3233_ = lean_uint8_dec_eq(v___x_3231_, v___x_3232_);
                    if v___x_3233_ == 0 {
                        if v___x_3228_ == 0 {
                            v___x_3234_ = leanh::lean_box(0);
                            v___x_3235_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3235_, 0, v_a_3221_);
                            leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                            return v___x_3235_;
                        } else {
                            v___x_3236_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                            v___x_3237_ = lean_uint8_dec_le(v___x_3236_, v___x_3231_);
                            if v___x_3237_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_3238_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                v___x_3239_ = lean_uint8_dec_le(v___x_3231_, v___x_3238_);
                                if v___x_3239_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_idx_3226_);
                                    leanh::lean_inc_ref(v_array_3225_);
                                    v_isSharedCheck_3269_ =
                                        (!leanh::lean_is_exclusive(v_a_3221_)) as u8;
                                    if v_isSharedCheck_3269_ == 0 {
                                        v_unused_3270_ = leanh::lean_ctor_get(v_a_3221_, 1);
                                        leanh::lean_dec(v_unused_3270_);
                                        v_unused_3271_ = leanh::lean_ctor_get(v_a_3221_, 0);
                                        leanh::lean_dec(v_unused_3271_);
                                        v___x_3241_ = v_a_3221_;
                                        v_isShared_3242_ = v_isSharedCheck_3269_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_3221_);
                                        v___x_3241_ = leanh::lean_box(0);
                                        v_isShared_3242_ = v_isSharedCheck_3269_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_3228_ == 0 {
                            v___x_3272_ = leanh::lean_box(0);
                            v___x_3273_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3273_, 0, v_a_3221_);
                            leanh::lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                            return v___x_3273_;
                        } else {
                            if v___x_3233_ == 0 {
                                v___x_3274_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
                                v___x_3275_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3275_, 0, v_a_3221_);
                                leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
                                return v___x_3275_;
                            } else {
                                leanh::lean_inc(v_idx_3226_);
                                leanh::lean_inc_ref(v_array_3225_);
                                v_isSharedCheck_3319_ =
                                    (!leanh::lean_is_exclusive(v_a_3221_)) as u8;
                                if v_isSharedCheck_3319_ == 0 {
                                    v_unused_3320_ = leanh::lean_ctor_get(v_a_3221_, 1);
                                    leanh::lean_dec(v_unused_3320_);
                                    v_unused_3321_ = leanh::lean_ctor_get(v_a_3221_, 0);
                                    leanh::lean_dec(v_unused_3321_);
                                    v___x_3277_ = v_a_3221_;
                                    v_isShared_3278_ = v_isSharedCheck_3319_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3221_);
                                    v___x_3277_ = leanh::lean_box(0);
                                    v_isShared_3278_ = v_isSharedCheck_3319_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3223_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3224_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3224_, 0, v_a_3221_);
                leanh::lean_ctor_set(v___x_3224_, 1, v___x_3223_);
                return v___x_3224_;
            }
            2 => {
                v___x_3243_ = leanh::lean_unsigned_to_nat(1);
                v___x_3244_ = lean_nat_add(v_idx_3226_, v___x_3243_);
                leanh::lean_dec(v_idx_3226_);
                if v_isShared_3242_ == 0 {
                    leanh::lean_ctor_set(v___x_3241_, 1, v___x_3244_);
                    v_it_x27_3246_ = v___x_3241_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_array_3225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 1, v___x_3244_);
                    v_it_x27_3246_ = v_reuseFailAlloc_3268_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3247_ = lean_uint8_to_uint32(v___x_3231_);
                v___x_3248_ = lean_uint32_to_uint8(v___x_3247_);
                v___x_3249_ = lean_uint8_sub(v___x_3248_, v___x_3236_);
                v___x_3250_ = lean_uint8_to_nat(v___x_3249_);
                v___x_3251_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3246_, v___x_3250_);
                v_fst_3252_ = leanh::lean_ctor_get(v___x_3251_, 0);
                v_snd_3253_ = leanh::lean_ctor_get(v___x_3251_, 1);
                v_isSharedCheck_3267_ = (!leanh::lean_is_exclusive(v___x_3251_)) as u8;
                if v_isSharedCheck_3267_ == 0 {
                    v___x_3255_ = v___x_3251_;
                    v_isShared_3256_ = v_isSharedCheck_3267_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3253_);
                    leanh::lean_inc(v_fst_3252_);
                    leanh::lean_dec(v___x_3251_);
                    v___x_3255_ = leanh::lean_box(0);
                    v_isShared_3256_ = v_isSharedCheck_3267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3257_ = leanh::lean_unsigned_to_nat(0);
                v___x_3258_ = lean_nat_dec_eq(v_fst_3252_, v___x_3257_);
                if v___x_3258_ == 0 {
                    v___x_3259_ = lean_nat_to_int(v_fst_3252_);
                    if v_isShared_3256_ == 0 {
                        leanh::lean_ctor_set(v___x_3255_, 1, v___x_3259_);
                        leanh::lean_ctor_set(v___x_3255_, 0, v_snd_3253_);
                        v___x_3261_ = v___x_3255_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3262_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_snd_3253_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3259_);
                        v___x_3261_ = v_reuseFailAlloc_3262_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_3252_);
                    v___x_3263_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3256_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3255_, 1);
                        leanh::lean_ctor_set(v___x_3255_, 1, v___x_3263_);
                        leanh::lean_ctor_set(v___x_3255_, 0, v_snd_3253_);
                        v___x_3265_ = v___x_3255_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3266_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_snd_3253_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
                        v___x_3265_ = v_reuseFailAlloc_3266_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3261_;
            }
            6 => {
                return v___x_3265_;
            }
            7 => {
                v___x_3279_ = leanh::lean_unsigned_to_nat(1);
                v___x_3280_ = lean_nat_add(v_idx_3226_, v___x_3279_);
                leanh::lean_dec(v_idx_3226_);
                leanh::lean_inc(v___x_3280_);
                leanh::lean_inc_ref(v_array_3225_);
                if v_isShared_3278_ == 0 {
                    leanh::lean_ctor_set(v___x_3277_, 1, v___x_3280_);
                    v___x_3282_ = v___x_3277_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_array_3225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3318_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3286_ = lean_nat_dec_lt(v___x_3280_, v___x_3227_);
                if v___x_3286_ == 0 {
                    leanh::lean_dec(v___x_3280_);
                    leanh::lean_dec_ref(v_array_3225_);
                    v___x_3287_ = leanh::lean_box(0);
                    v___x_3288_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3288_, 0, v___x_3282_);
                    leanh::lean_ctor_set(v___x_3288_, 1, v___x_3287_);
                    return v___x_3288_;
                } else {
                    v_c_3289_ = lean_byte_array_fget(v_array_3225_, v___x_3280_);
                    v___x_3290_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_3291_ = lean_uint8_dec_le(v___x_3290_, v_c_3289_);
                    if v___x_3291_ == 0 {
                        leanh::lean_dec(v___x_3280_);
                        leanh::lean_dec_ref(v_array_3225_);
                        state = 9;
                        continue;
                    } else {
                        v___x_3292_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_3293_ = lean_uint8_dec_le(v_c_3289_, v___x_3292_);
                        if v___x_3293_ == 0 {
                            leanh::lean_dec(v___x_3280_);
                            leanh::lean_dec_ref(v_array_3225_);
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_3282_);
                            v___x_3294_ = lean_nat_add(v___x_3280_, v___x_3279_);
                            leanh::lean_dec(v___x_3280_);
                            v_it_x27_3295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_it_x27_3295_, 0, v_array_3225_);
                            leanh::lean_ctor_set(v_it_x27_3295_, 1, v___x_3294_);
                            v___x_3296_ = lean_uint8_to_uint32(v_c_3289_);
                            v___x_3297_ = lean_uint32_to_uint8(v___x_3296_);
                            v___x_3298_ = lean_uint8_sub(v___x_3297_, v___x_3290_);
                            v___x_3299_ = lean_uint8_to_nat(v___x_3298_);
                            v___x_3300_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3295_, v___x_3299_);
                            v_fst_3301_ = leanh::lean_ctor_get(v___x_3300_, 0);
                            v_snd_3302_ = leanh::lean_ctor_get(v___x_3300_, 1);
                            v_isSharedCheck_3317_ =
                                (!leanh::lean_is_exclusive(v___x_3300_)) as u8;
                            if v_isSharedCheck_3317_ == 0 {
                                v___x_3304_ = v___x_3300_;
                                v_isShared_3305_ = v_isSharedCheck_3317_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_3302_);
                                leanh::lean_inc(v_fst_3301_);
                                leanh::lean_dec(v___x_3300_);
                                v___x_3304_ = leanh::lean_box(0);
                                v_isShared_3305_ = v_isSharedCheck_3317_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                v___x_3284_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3285_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3285_, 0, v___x_3282_);
                leanh::lean_ctor_set(v___x_3285_, 1, v___x_3284_);
                return v___x_3285_;
            }
            10 => {
                v___x_3306_ = leanh::lean_unsigned_to_nat(0);
                v___x_3307_ = lean_nat_dec_eq(v_fst_3301_, v___x_3306_);
                if v___x_3307_ == 0 {
                    v___x_3308_ = lean_nat_to_int(v_fst_3301_);
                    v___x_3309_ = lean_int_neg(v___x_3308_);
                    leanh::lean_dec(v___x_3308_);
                    if v_isShared_3305_ == 0 {
                        leanh::lean_ctor_set(v___x_3304_, 1, v___x_3309_);
                        leanh::lean_ctor_set(v___x_3304_, 0, v_snd_3302_);
                        v___x_3311_ = v___x_3304_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_snd_3302_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3309_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_3301_);
                    v___x_3313_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3305_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3304_, 1);
                        leanh::lean_ctor_set(v___x_3304_, 1, v___x_3313_);
                        leanh::lean_ctor_set(v___x_3304_, 0, v_snd_3302_);
                        v___x_3315_ = v___x_3304_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3316_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_snd_3302_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3313_);
                        v___x_3315_ = v_reuseFailAlloc_3316_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_3311_;
            }
            12 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(
    mut v_a_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v_got_3333_: u8 = 0;
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: u8 = 0;
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: u8 = 0;
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3369_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u32 = 0;
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3400_: u8 = 0;
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: u8 = 0;
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u32 = 0;
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: u8 = 0;
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3355_ = leanh::lean_ctor_get(v_a_3322_, 0);
                v_idx_3356_ = leanh::lean_ctor_get(v_a_3322_, 1);
                v___x_3357_ = lean_byte_array_size(v_array_3355_);
                v___x_3358_ = lean_nat_dec_lt(v_idx_3356_, v___x_3357_);
                if v___x_3358_ == 0 {
                    v___x_3359_ = leanh::lean_box(0);
                    v___x_3360_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3360_, 0, v_a_3322_);
                    leanh::lean_ctor_set(v___x_3360_, 1, v___x_3359_);
                    return v___x_3360_;
                } else {
                    v___x_3361_ = lean_byte_array_fget(v_array_3355_, v_idx_3356_);
                    v___x_3362_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
                    );
                    v___x_3363_ = lean_uint8_dec_eq(v___x_3361_, v___x_3362_);
                    if v___x_3363_ == 0 {
                        if v___x_3358_ == 0 {
                            v___x_3364_ = leanh::lean_box(0);
                            v___x_3365_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3365_, 0, v_a_3322_);
                            leanh::lean_ctor_set(v___x_3365_, 1, v___x_3364_);
                            return v___x_3365_;
                        } else {
                            v___x_3366_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                            v___x_3367_ = lean_uint8_dec_le(v___x_3366_, v___x_3361_);
                            if v___x_3367_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v___x_3368_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                v___x_3369_ = lean_uint8_dec_le(v___x_3361_, v___x_3368_);
                                if v___x_3369_ == 0 {
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_3370_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3371_ = lean_nat_add(v_idx_3356_, v___x_3370_);
                                    leanh::lean_inc_ref(v_array_3355_);
                                    v_it_x27_3372_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v_it_x27_3372_, 0, v_array_3355_);
                                    leanh::lean_ctor_set(v_it_x27_3372_, 1, v___x_3371_);
                                    v___x_3373_ = lean_uint8_to_uint32(v___x_3361_);
                                    v___x_3374_ = lean_uint32_to_uint8(v___x_3373_);
                                    v___x_3375_ = lean_uint8_sub(v___x_3374_, v___x_3366_);
                                    v___x_3376_ = lean_uint8_to_nat(v___x_3375_);
                                    v___x_3377_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3372_, v___x_3376_);
                                    v_fst_3378_ = leanh::lean_ctor_get(v___x_3377_, 0);
                                    v_snd_3379_ = leanh::lean_ctor_get(v___x_3377_, 1);
                                    v_isSharedCheck_3390_ =
                                        (!leanh::lean_is_exclusive(v___x_3377_)) as u8;
                                    if v_isSharedCheck_3390_ == 0 {
                                        v___x_3381_ = v___x_3377_;
                                        v_isShared_3382_ = v_isSharedCheck_3390_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_snd_3379_);
                                        leanh::lean_inc(v_fst_3378_);
                                        leanh::lean_dec(v___x_3377_);
                                        v___x_3381_ = leanh::lean_box(0);
                                        v_isShared_3382_ = v_isSharedCheck_3390_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_3358_ == 0 {
                            v___x_3391_ = leanh::lean_box(0);
                            v___x_3392_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3392_, 0, v_a_3322_);
                            leanh::lean_ctor_set(v___x_3392_, 1, v___x_3391_);
                            return v___x_3392_;
                        } else {
                            if v___x_3363_ == 0 {
                                v___x_3393_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
                                v___x_3394_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3394_, 0, v_a_3322_);
                                leanh::lean_ctor_set(v___x_3394_, 1, v___x_3393_);
                                return v___x_3394_;
                            } else {
                                v___x_3395_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3396_ = lean_nat_add(v_idx_3356_, v___x_3395_);
                                v___x_3397_ = lean_nat_dec_lt(v___x_3396_, v___x_3357_);
                                if v___x_3397_ == 0 {
                                    leanh::lean_dec(v___x_3396_);
                                    v___x_3398_ = leanh::lean_box(0);
                                    v___x_3399_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3399_, 0, v_a_3322_);
                                    leanh::lean_ctor_set(v___x_3399_, 1, v___x_3398_);
                                    return v___x_3399_;
                                } else {
                                    v_c_3400_ = lean_byte_array_fget(v_array_3355_, v___x_3396_);
                                    v___x_3401_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                                    v___x_3402_ = lean_uint8_dec_le(v___x_3401_, v_c_3400_);
                                    if v___x_3402_ == 0 {
                                        leanh::lean_dec(v___x_3396_);
                                        state = 5;
                                        continue;
                                    } else {
                                        v___x_3403_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                        v___x_3404_ = lean_uint8_dec_le(v_c_3400_, v___x_3403_);
                                        if v___x_3404_ == 0 {
                                            leanh::lean_dec(v___x_3396_);
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_3405_ = lean_nat_add(v___x_3396_, v___x_3395_);
                                            leanh::lean_dec(v___x_3396_);
                                            leanh::lean_inc_ref(v_array_3355_);
                                            v_it_x27_3406_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_it_x27_3406_,
                                                0,
                                                v_array_3355_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_it_x27_3406_,
                                                1,
                                                v___x_3405_,
                                            );
                                            v___x_3407_ = lean_uint8_to_uint32(v_c_3400_);
                                            v___x_3408_ = lean_uint32_to_uint8(v___x_3407_);
                                            v___x_3409_ = lean_uint8_sub(v___x_3408_, v___x_3401_);
                                            v___x_3410_ = lean_uint8_to_nat(v___x_3409_);
                                            v___x_3411_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3406_, v___x_3410_);
                                            v_fst_3412_ =
                                                leanh::lean_ctor_get(v___x_3411_, 0);
                                            v_snd_3413_ =
                                                leanh::lean_ctor_get(v___x_3411_, 1);
                                            v_isSharedCheck_3425_ =
                                                (!leanh::lean_is_exclusive(v___x_3411_))
                                                    as u8;
                                            if v_isSharedCheck_3425_ == 0 {
                                                v___x_3415_ = v___x_3411_;
                                                v_isShared_3416_ = v_isSharedCheck_3425_;
                                                state = 8;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_snd_3413_);
                                                leanh::lean_inc(v_fst_3412_);
                                                leanh::lean_dec(v___x_3411_);
                                                v___x_3415_ = leanh::lean_box(0);
                                                v_isShared_3416_ = v_isSharedCheck_3425_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_array_3326_ = leanh::lean_ctor_get(v_pos_3324_, 0);
                v_idx_3327_ = leanh::lean_ctor_get(v_pos_3324_, 1);
                v___x_3328_ = lean_byte_array_size(v_array_3326_);
                v___x_3329_ = lean_nat_dec_lt(v_idx_3327_, v___x_3328_);
                if v___x_3329_ == 0 {
                    leanh::lean_dec(v_res_3325_);
                    v___x_3330_ = leanh::lean_box(0);
                    v___x_3331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3331_, 0, v_pos_3324_);
                    leanh::lean_ctor_set(v___x_3331_, 1, v___x_3330_);
                    return v___x_3331_;
                } else {
                    v___x_3332_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3333_ = lean_byte_array_fget(v_array_3326_, v_idx_3327_);
                    v___x_3334_ = lean_uint8_dec_eq(v_got_3333_, v___x_3332_);
                    if v___x_3334_ == 0 {
                        leanh::lean_dec(v_res_3325_);
                        v___x_3335_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        v___x_3336_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3336_, 0, v_pos_3324_);
                        leanh::lean_ctor_set(v___x_3336_, 1, v___x_3335_);
                        return v___x_3336_;
                    } else {
                        leanh::lean_inc(v_idx_3327_);
                        leanh::lean_inc_ref(v_array_3326_);
                        v_isSharedCheck_3346_ =
                            (!leanh::lean_is_exclusive(v_pos_3324_)) as u8;
                        if v_isSharedCheck_3346_ == 0 {
                            v_unused_3347_ = leanh::lean_ctor_get(v_pos_3324_, 1);
                            leanh::lean_dec(v_unused_3347_);
                            v_unused_3348_ = leanh::lean_ctor_get(v_pos_3324_, 0);
                            leanh::lean_dec(v_unused_3348_);
                            v___x_3338_ = v_pos_3324_;
                            v_isShared_3339_ = v_isSharedCheck_3346_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3324_);
                            v___x_3338_ = leanh::lean_box(0);
                            v_isShared_3339_ = v_isSharedCheck_3346_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3340_ = leanh::lean_unsigned_to_nat(1);
                v___x_3341_ = lean_nat_add(v_idx_3327_, v___x_3340_);
                leanh::lean_dec(v_idx_3327_);
                if v_isShared_3339_ == 0 {
                    leanh::lean_ctor_set(v___x_3338_, 1, v___x_3341_);
                    v___x_3343_ = v___x_3338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_array_3326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3341_);
                    v___x_3343_ = v_reuseFailAlloc_3345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3344_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3344_, 0, v___x_3343_);
                leanh::lean_ctor_set(v___x_3344_, 1, v_res_3325_);
                return v___x_3344_;
            }
            4 => {
                v___x_3350_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3351_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3351_, 0, v_a_3322_);
                leanh::lean_ctor_set(v___x_3351_, 1, v___x_3350_);
                return v___x_3351_;
            }
            5 => {
                v___x_3353_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3354_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3354_, 0, v_a_3322_);
                leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                return v___x_3354_;
            }
            6 => {
                v___x_3383_ = leanh::lean_unsigned_to_nat(0);
                v___x_3384_ = lean_nat_dec_eq(v_fst_3378_, v___x_3383_);
                if v___x_3384_ == 0 {
                    leanh::lean_del_object(v___x_3381_);
                    leanh::lean_dec_ref(v_a_3322_);
                    v___x_3385_ = lean_nat_to_int(v_fst_3378_);
                    v_pos_3324_ = v_snd_3379_;
                    v_res_3325_ = v___x_3385_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_3379_);
                    leanh::lean_dec(v_fst_3378_);
                    v___x_3386_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3382_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3381_, 1);
                        leanh::lean_ctor_set(v___x_3381_, 1, v___x_3386_);
                        leanh::lean_ctor_set(v___x_3381_, 0, v_a_3322_);
                        v___x_3388_ = v___x_3381_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3389_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3322_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3386_);
                        v___x_3388_ = v_reuseFailAlloc_3389_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3388_;
            }
            8 => {
                v___x_3417_ = leanh::lean_unsigned_to_nat(0);
                v___x_3418_ = lean_nat_dec_eq(v_fst_3412_, v___x_3417_);
                if v___x_3418_ == 0 {
                    leanh::lean_del_object(v___x_3415_);
                    leanh::lean_dec_ref(v_a_3322_);
                    v___x_3419_ = lean_nat_to_int(v_fst_3412_);
                    v___x_3420_ = lean_int_neg(v___x_3419_);
                    leanh::lean_dec(v___x_3419_);
                    v_pos_3324_ = v_snd_3413_;
                    v_res_3325_ = v___x_3420_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_3413_);
                    leanh::lean_dec(v_fst_3412_);
                    v___x_3421_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3416_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3415_, 1);
                        leanh::lean_ctor_set(v___x_3415_, 1, v___x_3421_);
                        leanh::lean_ctor_set(v___x_3415_, 0, v_a_3322_);
                        v___x_3423_ = v___x_3415_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3424_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3322_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3421_);
                        v___x_3423_ = v_reuseFailAlloc_3424_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_3423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(
    mut v_a_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ = lean_nat_to_int(v_a_3426_);
    return v___x_3427_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(
    mut v_acc_3428_: *mut leanh::LeanObject,
    mut v_a_3429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: u8 = 0;
    let mut v_got_3452_: u8 = 0;
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: u32 = 0;
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3499_: u8 = 0;
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u32 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3430_ = leanh::lean_ctor_get(v_a_3429_, 0);
                v_idx_3431_ = leanh::lean_ctor_get(v_a_3429_, 1);
                leanh::lean_inc(v_idx_3431_);
                v___x_3468_ = lean_byte_array_size(v_array_3430_);
                v___x_3469_ = lean_nat_dec_lt(v_idx_3431_, v___x_3468_);
                if v___x_3469_ == 0 {
                    v___x_3470_ = leanh::lean_box(0);
                    leanh::lean_inc(v_idx_3431_);
                    v_pos_3433_ = v_a_3429_;
                    v_idx_3434_ = v_idx_3431_;
                    v_err_3435_ = v___x_3470_;
                    state = 1;
                    continue;
                } else {
                    v___x_3471_ = lean_byte_array_fget(v_array_3430_, v_idx_3431_);
                    v___x_3472_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
                    );
                    v___x_3473_ = lean_uint8_dec_eq(v___x_3471_, v___x_3472_);
                    if v___x_3473_ == 0 {
                        if v___x_3469_ == 0 {
                            v___x_3474_ = leanh::lean_box(0);
                            leanh::lean_inc(v_idx_3431_);
                            v_pos_3433_ = v_a_3429_;
                            v_idx_3434_ = v_idx_3431_;
                            v_err_3435_ = v___x_3474_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3475_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                            v___x_3476_ = lean_uint8_dec_le(v___x_3475_, v___x_3471_);
                            if v___x_3476_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                v___x_3477_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                v___x_3478_ = lean_uint8_dec_le(v___x_3471_, v___x_3477_);
                                if v___x_3478_ == 0 {
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3479_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3480_ = lean_nat_add(v_idx_3431_, v___x_3479_);
                                    leanh::lean_inc_ref(v_array_3430_);
                                    v_it_x27_3481_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v_it_x27_3481_, 0, v_array_3430_);
                                    leanh::lean_ctor_set(v_it_x27_3481_, 1, v___x_3480_);
                                    v___x_3482_ = lean_uint8_to_uint32(v___x_3471_);
                                    v___x_3483_ = lean_uint32_to_uint8(v___x_3482_);
                                    v___x_3484_ = lean_uint8_sub(v___x_3483_, v___x_3475_);
                                    v___x_3485_ = lean_uint8_to_nat(v___x_3484_);
                                    v___x_3486_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3481_, v___x_3485_);
                                    v_fst_3487_ = leanh::lean_ctor_get(v___x_3486_, 0);
                                    leanh::lean_inc(v_fst_3487_);
                                    v_snd_3488_ = leanh::lean_ctor_get(v___x_3486_, 1);
                                    leanh::lean_inc(v_snd_3488_);
                                    leanh::lean_dec_ref(v___x_3486_);
                                    v___x_3489_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_3490_ = lean_nat_dec_eq(v_fst_3487_, v___x_3489_);
                                    if v___x_3490_ == 0 {
                                        leanh::lean_dec_ref(v_a_3429_);
                                        v___x_3491_ = lean_nat_to_int(v_fst_3487_);
                                        v_pos_3444_ = v_snd_3488_;
                                        v_res_3445_ = v___x_3491_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_snd_3488_);
                                        leanh::lean_dec(v_fst_3487_);
                                        v___x_3492_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                                        leanh::lean_inc(v_idx_3431_);
                                        v_pos_3433_ = v_a_3429_;
                                        v_idx_3434_ = v_idx_3431_;
                                        v_err_3435_ = v___x_3492_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_3469_ == 0 {
                            v___x_3493_ = leanh::lean_box(0);
                            leanh::lean_inc(v_idx_3431_);
                            v_pos_3433_ = v_a_3429_;
                            v_idx_3434_ = v_idx_3431_;
                            v_err_3435_ = v___x_3493_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_3473_ == 0 {
                                v___x_3494_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
                                leanh::lean_inc(v_idx_3431_);
                                v_pos_3433_ = v_a_3429_;
                                v_idx_3434_ = v_idx_3431_;
                                v_err_3435_ = v___x_3494_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3495_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3496_ = lean_nat_add(v_idx_3431_, v___x_3495_);
                                v___x_3497_ = lean_nat_dec_lt(v___x_3496_, v___x_3468_);
                                if v___x_3497_ == 0 {
                                    leanh::lean_dec(v___x_3496_);
                                    v___x_3498_ = leanh::lean_box(0);
                                    leanh::lean_inc(v_idx_3431_);
                                    v_pos_3433_ = v_a_3429_;
                                    v_idx_3434_ = v_idx_3431_;
                                    v_err_3435_ = v___x_3498_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_c_3499_ = lean_byte_array_fget(v_array_3430_, v___x_3496_);
                                    v___x_3500_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                                    v___x_3501_ = lean_uint8_dec_le(v___x_3500_, v_c_3499_);
                                    if v___x_3501_ == 0 {
                                        leanh::lean_dec(v___x_3496_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3502_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                        v___x_3503_ = lean_uint8_dec_le(v_c_3499_, v___x_3502_);
                                        if v___x_3503_ == 0 {
                                            leanh::lean_dec(v___x_3496_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_3504_ = lean_nat_add(v___x_3496_, v___x_3495_);
                                            leanh::lean_dec(v___x_3496_);
                                            leanh::lean_inc_ref(v_array_3430_);
                                            v_it_x27_3505_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_it_x27_3505_,
                                                0,
                                                v_array_3430_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_it_x27_3505_,
                                                1,
                                                v___x_3504_,
                                            );
                                            v___x_3506_ = lean_uint8_to_uint32(v_c_3499_);
                                            v___x_3507_ = lean_uint32_to_uint8(v___x_3506_);
                                            v___x_3508_ = lean_uint8_sub(v___x_3507_, v___x_3500_);
                                            v___x_3509_ = lean_uint8_to_nat(v___x_3508_);
                                            v___x_3510_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3505_, v___x_3509_);
                                            v_fst_3511_ =
                                                leanh::lean_ctor_get(v___x_3510_, 0);
                                            leanh::lean_inc(v_fst_3511_);
                                            v_snd_3512_ =
                                                leanh::lean_ctor_get(v___x_3510_, 1);
                                            leanh::lean_inc(v_snd_3512_);
                                            leanh::lean_dec_ref(v___x_3510_);
                                            v___x_3513_ = leanh::lean_unsigned_to_nat(0);
                                            v___x_3514_ = lean_nat_dec_eq(v_fst_3511_, v___x_3513_);
                                            if v___x_3514_ == 0 {
                                                leanh::lean_dec_ref(v_a_3429_);
                                                v___x_3515_ = lean_nat_to_int(v_fst_3511_);
                                                v___x_3516_ = lean_int_neg(v___x_3515_);
                                                leanh::lean_dec(v___x_3515_);
                                                v_pos_3444_ = v_snd_3512_;
                                                v_res_3445_ = v___x_3516_;
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_snd_3512_);
                                                leanh::lean_dec(v_fst_3511_);
                                                v___x_3517_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                                                leanh::lean_inc(v_idx_3431_);
                                                v_pos_3433_ = v_a_3429_;
                                                v_idx_3434_ = v_idx_3431_;
                                                v_err_3435_ = v___x_3517_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3436_ = lean_nat_dec_eq(v_idx_3431_, v_idx_3434_);
                leanh::lean_dec(v_idx_3434_);
                leanh::lean_dec(v_idx_3431_);
                if v___x_3436_ == 0 {
                    leanh::lean_dec_ref(v_acc_3428_);
                    leanh::lean_inc(v_err_3435_);
                    v___x_3437_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3437_, 0, v_pos_3433_);
                    leanh::lean_ctor_set(v___x_3437_, 1, v_err_3435_);
                    return v___x_3437_;
                } else {
                    v___x_3438_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3438_, 0, v_pos_3433_);
                    leanh::lean_ctor_set(v___x_3438_, 1, v_acc_3428_);
                    return v___x_3438_;
                }
            }
            2 => {
                v___x_3440_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                leanh::lean_inc(v_idx_3431_);
                v_pos_3433_ = v_a_3429_;
                v_idx_3434_ = v_idx_3431_;
                v_err_3435_ = v___x_3440_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3442_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                leanh::lean_inc(v_idx_3431_);
                v_pos_3433_ = v_a_3429_;
                v_idx_3434_ = v_idx_3431_;
                v_err_3435_ = v___x_3442_;
                state = 1;
                continue;
            }
            4 => {
                v_array_3446_ = leanh::lean_ctor_get(v_pos_3444_, 0);
                v_idx_3447_ = leanh::lean_ctor_get(v_pos_3444_, 1);
                leanh::lean_inc(v_idx_3447_);
                v___x_3448_ = lean_byte_array_size(v_array_3446_);
                v___x_3449_ = lean_nat_dec_lt(v_idx_3447_, v___x_3448_);
                if v___x_3449_ == 0 {
                    leanh::lean_dec(v_res_3445_);
                    v___x_3450_ = leanh::lean_box(0);
                    v_pos_3433_ = v_pos_3444_;
                    v_idx_3434_ = v_idx_3447_;
                    v_err_3435_ = v___x_3450_;
                    state = 1;
                    continue;
                } else {
                    v___x_3451_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3452_ = lean_byte_array_fget(v_array_3446_, v_idx_3447_);
                    v___x_3453_ = lean_uint8_dec_eq(v_got_3452_, v___x_3451_);
                    if v___x_3453_ == 0 {
                        leanh::lean_dec(v_res_3445_);
                        v___x_3454_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        v_pos_3433_ = v_pos_3444_;
                        v_idx_3434_ = v_idx_3447_;
                        v_err_3435_ = v___x_3454_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_array_3446_);
                        leanh::lean_dec(v_idx_3431_);
                        v_isSharedCheck_3465_ =
                            (!leanh::lean_is_exclusive(v_pos_3444_)) as u8;
                        if v_isSharedCheck_3465_ == 0 {
                            v_unused_3466_ = leanh::lean_ctor_get(v_pos_3444_, 1);
                            leanh::lean_dec(v_unused_3466_);
                            v_unused_3467_ = leanh::lean_ctor_get(v_pos_3444_, 0);
                            leanh::lean_dec(v_unused_3467_);
                            v___x_3456_ = v_pos_3444_;
                            v_isShared_3457_ = v_isSharedCheck_3465_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3444_);
                            v___x_3456_ = leanh::lean_box(0);
                            v_isShared_3457_ = v_isSharedCheck_3465_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_3458_ = leanh::lean_unsigned_to_nat(1);
                v___x_3459_ = lean_nat_add(v_idx_3447_, v___x_3458_);
                leanh::lean_dec(v_idx_3447_);
                if v_isShared_3457_ == 0 {
                    leanh::lean_ctor_set(v___x_3456_, 1, v___x_3459_);
                    v___x_3461_ = v___x_3456_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_array_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3459_);
                    v___x_3461_ = v_reuseFailAlloc_3464_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3462_ = lean_array_push(v_acc_3428_, v_res_3445_);
                v_acc_3428_ = v___x_3462_;
                v_a_3429_ = v___x_3461_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(
    mut v_a_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v_array_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v_got_3537_: u8 = 0;
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3554_: u8 = 0;
    let mut v_unused_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3521_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0;
                v___x_3522_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_3521_, v_a_3520_);
                if leanh::lean_obj_tag(v___x_3522_) == 0 {
                    v_pos_3523_ = leanh::lean_ctor_get(v___x_3522_, 0);
                    v_res_3524_ = leanh::lean_ctor_get(v___x_3522_, 1);
                    v_isSharedCheck_3557_ = (!leanh::lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3557_ == 0 {
                        v___x_3526_ = v___x_3522_;
                        v_isShared_3527_ = v_isSharedCheck_3557_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_3524_);
                        leanh::lean_inc(v_pos_3523_);
                        leanh::lean_dec(v___x_3522_);
                        v___x_3526_ = leanh::lean_box(0);
                        v_isShared_3527_ = v_isSharedCheck_3557_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3522_;
                }
            }
            1 => {
                v_array_3528_ = leanh::lean_ctor_get(v_pos_3523_, 0);
                v_idx_3529_ = leanh::lean_ctor_get(v_pos_3523_, 1);
                v___x_3530_ = lean_byte_array_size(v_array_3528_);
                v___x_3531_ = lean_nat_dec_lt(v_idx_3529_, v___x_3530_);
                if v___x_3531_ == 0 {
                    leanh::lean_dec(v_res_3524_);
                    v___x_3532_ = leanh::lean_box(0);
                    if v_isShared_3527_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3526_, 1);
                        leanh::lean_ctor_set(v___x_3526_, 1, v___x_3532_);
                        v___x_3534_ = v___x_3526_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3535_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_pos_3523_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3532_);
                        v___x_3534_ = v_reuseFailAlloc_3535_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3536_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v_got_3537_ = lean_byte_array_fget(v_array_3528_, v_idx_3529_);
                    v___x_3538_ = lean_uint8_dec_eq(v_got_3537_, v___x_3536_);
                    if v___x_3538_ == 0 {
                        leanh::lean_dec(v_res_3524_);
                        v___x_3539_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        if v_isShared_3527_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3526_, 1);
                            leanh::lean_ctor_set(v___x_3526_, 1, v___x_3539_);
                            v___x_3541_ = v___x_3526_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3542_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_pos_3523_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 1, v___x_3539_);
                            v___x_3541_ = v_reuseFailAlloc_3542_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_3529_);
                        leanh::lean_inc_ref(v_array_3528_);
                        v_isSharedCheck_3554_ =
                            (!leanh::lean_is_exclusive(v_pos_3523_)) as u8;
                        if v_isSharedCheck_3554_ == 0 {
                            v_unused_3555_ = leanh::lean_ctor_get(v_pos_3523_, 1);
                            leanh::lean_dec(v_unused_3555_);
                            v_unused_3556_ = leanh::lean_ctor_get(v_pos_3523_, 0);
                            leanh::lean_dec(v_unused_3556_);
                            v___x_3544_ = v_pos_3523_;
                            v_isShared_3545_ = v_isSharedCheck_3554_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3523_);
                            v___x_3544_ = leanh::lean_box(0);
                            v_isShared_3545_ = v_isSharedCheck_3554_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3534_;
            }
            3 => {
                return v___x_3541_;
            }
            4 => {
                v___x_3546_ = leanh::lean_unsigned_to_nat(1);
                v___x_3547_ = lean_nat_add(v_idx_3529_, v___x_3546_);
                leanh::lean_dec(v_idx_3529_);
                if v_isShared_3545_ == 0 {
                    leanh::lean_ctor_set(v___x_3544_, 1, v___x_3547_);
                    v___x_3549_ = v___x_3544_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_array_3528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___x_3547_);
                    v___x_3549_ = v_reuseFailAlloc_3553_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3527_ == 0 {
                    leanh::lean_ctor_set(v___x_3526_, 0, v___x_3549_);
                    v___x_3551_ = v___x_3526_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3552_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_res_3524_);
                    v___x_3551_ = v_reuseFailAlloc_3552_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(
    mut v_a_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v_got_3566_: u8 = 0;
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3583_: u8 = 0;
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u32 = 0;
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v_array_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: u8 = 0;
    let mut v_got_3609_: u8 = 0;
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_pos_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_unused_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v_reuseFailAlloc_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut v_unused_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3559_ = leanh::lean_ctor_get(v_a_3558_, 0);
                v_idx_3560_ = leanh::lean_ctor_get(v_a_3558_, 1);
                v___x_3561_ = lean_byte_array_size(v_array_3559_);
                v___x_3562_ = lean_nat_dec_lt(v_idx_3560_, v___x_3561_);
                if v___x_3562_ == 0 {
                    v___x_3563_ = leanh::lean_box(0);
                    v___x_3564_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3564_, 0, v_a_3558_);
                    leanh::lean_ctor_set(v___x_3564_, 1, v___x_3563_);
                    return v___x_3564_;
                } else {
                    v___x_3565_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
                    );
                    v_got_3566_ = lean_byte_array_fget(v_array_3559_, v_idx_3560_);
                    v___x_3567_ = lean_uint8_dec_eq(v_got_3566_, v___x_3565_);
                    if v___x_3567_ == 0 {
                        v___x_3568_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5,
                        );
                        v___x_3569_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3569_, 0, v_a_3558_);
                        leanh::lean_ctor_set(v___x_3569_, 1, v___x_3568_);
                        return v___x_3569_;
                    } else {
                        leanh::lean_inc(v_idx_3560_);
                        leanh::lean_inc_ref(v_array_3559_);
                        v_isSharedCheck_3652_ = (!leanh::lean_is_exclusive(v_a_3558_)) as u8;
                        if v_isSharedCheck_3652_ == 0 {
                            v_unused_3653_ = leanh::lean_ctor_get(v_a_3558_, 1);
                            leanh::lean_dec(v_unused_3653_);
                            v_unused_3654_ = leanh::lean_ctor_get(v_a_3558_, 0);
                            leanh::lean_dec(v_unused_3654_);
                            v___x_3571_ = v_a_3558_;
                            v_isShared_3572_ = v_isSharedCheck_3652_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3558_);
                            v___x_3571_ = leanh::lean_box(0);
                            v_isShared_3572_ = v_isSharedCheck_3652_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3573_ = leanh::lean_unsigned_to_nat(1);
                v___x_3574_ = lean_nat_add(v_idx_3560_, v___x_3573_);
                leanh::lean_dec(v_idx_3560_);
                leanh::lean_inc(v___x_3574_);
                leanh::lean_inc_ref(v_array_3559_);
                if v_isShared_3572_ == 0 {
                    leanh::lean_ctor_set(v___x_3571_, 1, v___x_3574_);
                    v___x_3576_ = v___x_3571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_array_3559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3580_ = lean_nat_dec_lt(v___x_3574_, v___x_3561_);
                if v___x_3580_ == 0 {
                    leanh::lean_dec(v___x_3574_);
                    leanh::lean_dec_ref(v_array_3559_);
                    v___x_3581_ = leanh::lean_box(0);
                    v___x_3582_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3582_, 0, v___x_3576_);
                    leanh::lean_ctor_set(v___x_3582_, 1, v___x_3581_);
                    return v___x_3582_;
                } else {
                    v_c_3583_ = lean_byte_array_fget(v_array_3559_, v___x_3574_);
                    v___x_3584_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_3585_ = lean_uint8_dec_le(v___x_3584_, v_c_3583_);
                    if v___x_3585_ == 0 {
                        leanh::lean_dec(v___x_3574_);
                        leanh::lean_dec_ref(v_array_3559_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3586_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_3587_ = lean_uint8_dec_le(v_c_3583_, v___x_3586_);
                        if v___x_3587_ == 0 {
                            leanh::lean_dec(v___x_3574_);
                            leanh::lean_dec_ref(v_array_3559_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_3576_);
                            v___x_3588_ = lean_nat_add(v___x_3574_, v___x_3573_);
                            leanh::lean_dec(v___x_3574_);
                            v_it_x27_3589_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_it_x27_3589_, 0, v_array_3559_);
                            leanh::lean_ctor_set(v_it_x27_3589_, 1, v___x_3588_);
                            v___x_3590_ = lean_uint8_to_uint32(v_c_3583_);
                            v___x_3591_ = lean_uint32_to_uint8(v___x_3590_);
                            v___x_3592_ = lean_uint8_sub(v___x_3591_, v___x_3584_);
                            v___x_3593_ = lean_uint8_to_nat(v___x_3592_);
                            v___x_3594_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3589_, v___x_3593_);
                            v_fst_3595_ = leanh::lean_ctor_get(v___x_3594_, 0);
                            v_snd_3596_ = leanh::lean_ctor_get(v___x_3594_, 1);
                            v_isSharedCheck_3650_ =
                                (!leanh::lean_is_exclusive(v___x_3594_)) as u8;
                            if v_isSharedCheck_3650_ == 0 {
                                v___x_3598_ = v___x_3594_;
                                v_isShared_3599_ = v_isSharedCheck_3650_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_3596_);
                                leanh::lean_inc(v_fst_3595_);
                                leanh::lean_dec(v___x_3594_);
                                v___x_3598_ = leanh::lean_box(0);
                                v_isShared_3599_ = v_isSharedCheck_3650_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3578_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3579_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3579_, 0, v___x_3576_);
                leanh::lean_ctor_set(v___x_3579_, 1, v___x_3578_);
                return v___x_3579_;
            }
            4 => {
                v___x_3600_ = leanh::lean_unsigned_to_nat(0);
                v___x_3601_ = lean_nat_dec_eq(v_fst_3595_, v___x_3600_);
                if v___x_3601_ == 0 {
                    v_array_3602_ = leanh::lean_ctor_get(v_snd_3596_, 0);
                    v_idx_3603_ = leanh::lean_ctor_get(v_snd_3596_, 1);
                    v___x_3604_ = lean_byte_array_size(v_array_3602_);
                    v___x_3605_ = lean_nat_dec_lt(v_idx_3603_, v___x_3604_);
                    if v___x_3605_ == 0 {
                        leanh::lean_del_object(v___x_3598_);
                        leanh::lean_dec(v_fst_3595_);
                        v___x_3606_ = leanh::lean_box(0);
                        v___x_3607_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3607_, 0, v_snd_3596_);
                        leanh::lean_ctor_set(v___x_3607_, 1, v___x_3606_);
                        return v___x_3607_;
                    } else {
                        v___x_3608_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                        v_got_3609_ = lean_byte_array_fget(v_array_3602_, v_idx_3603_);
                        v___x_3610_ = lean_uint8_dec_eq(v_got_3609_, v___x_3608_);
                        if v___x_3610_ == 0 {
                            leanh::lean_del_object(v___x_3598_);
                            leanh::lean_dec(v_fst_3595_);
                            v___x_3611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                            v___x_3612_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3612_, 0, v_snd_3596_);
                            leanh::lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                            return v___x_3612_;
                        } else {
                            leanh::lean_inc(v_idx_3603_);
                            leanh::lean_inc_ref(v_array_3602_);
                            v_isSharedCheck_3645_ =
                                (!leanh::lean_is_exclusive(v_snd_3596_)) as u8;
                            if v_isSharedCheck_3645_ == 0 {
                                v_unused_3646_ = leanh::lean_ctor_get(v_snd_3596_, 1);
                                leanh::lean_dec(v_unused_3646_);
                                v_unused_3647_ = leanh::lean_ctor_get(v_snd_3596_, 0);
                                leanh::lean_dec(v_unused_3647_);
                                v___x_3614_ = v_snd_3596_;
                                v_isShared_3615_ = v_isSharedCheck_3645_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v_snd_3596_);
                                v___x_3614_ = leanh::lean_box(0);
                                v_isShared_3615_ = v_isSharedCheck_3645_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3598_);
                    leanh::lean_dec(v_fst_3595_);
                    v___x_3648_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    v___x_3649_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3649_, 0, v_snd_3596_);
                    leanh::lean_ctor_set(v___x_3649_, 1, v___x_3648_);
                    return v___x_3649_;
                }
            }
            5 => {
                v___x_3616_ = lean_nat_add(v_idx_3603_, v___x_3573_);
                leanh::lean_dec(v_idx_3603_);
                if v_isShared_3615_ == 0 {
                    leanh::lean_ctor_set(v___x_3614_, 1, v___x_3616_);
                    v___x_3618_ = v___x_3614_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_array_3602_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3644_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3619_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_3618_);
                if leanh::lean_obj_tag(v___x_3619_) == 0 {
                    v_pos_3620_ = leanh::lean_ctor_get(v___x_3619_, 0);
                    v_res_3621_ = leanh::lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3634_ = (!leanh::lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3634_ == 0 {
                        v___x_3623_ = v___x_3619_;
                        v_isShared_3624_ = v_isSharedCheck_3634_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_3621_);
                        leanh::lean_inc(v_pos_3620_);
                        leanh::lean_dec(v___x_3619_);
                        v___x_3623_ = leanh::lean_box(0);
                        v_isShared_3624_ = v_isSharedCheck_3634_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3598_);
                    leanh::lean_dec(v_fst_3595_);
                    v_pos_3635_ = leanh::lean_ctor_get(v___x_3619_, 0);
                    v_err_3636_ = leanh::lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3643_ = (!leanh::lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3643_ == 0 {
                        v___x_3638_ = v___x_3619_;
                        v_isShared_3639_ = v_isSharedCheck_3643_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3636_);
                        leanh::lean_inc(v_pos_3635_);
                        leanh::lean_dec(v___x_3619_);
                        v___x_3638_ = leanh::lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3643_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3625_ = lean_nat_to_int(v_fst_3595_);
                v___x_3626_ = lean_int_neg(v___x_3625_);
                leanh::lean_dec(v___x_3625_);
                v___x_3627_ = lean_nat_abs(v___x_3626_);
                leanh::lean_dec(v___x_3626_);
                if v_isShared_3599_ == 0 {
                    leanh::lean_ctor_set(v___x_3598_, 1, v_res_3621_);
                    leanh::lean_ctor_set(v___x_3598_, 0, v___x_3627_);
                    v___x_3629_ = v___x_3598_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_res_3621_);
                    v___x_3629_ = v_reuseFailAlloc_3633_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3624_ == 0 {
                    leanh::lean_ctor_set(v___x_3623_, 1, v___x_3629_);
                    v___x_3631_ = v___x_3623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_pos_3620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___x_3629_);
                    v___x_3631_ = v_reuseFailAlloc_3632_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3631_;
            }
            10 => {
                if v_isShared_3639_ == 0 {
                    v___x_3641_ = v___x_3638_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3642_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_pos_3635_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_err_3636_);
                    v___x_3641_ = v_reuseFailAlloc_3642_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(
    mut v_acc_3655_: *mut leanh::LeanObject,
    mut v_a_3656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v_idx_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_unused_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_3656_);
                v___x_3674_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_3656_);
                if leanh::lean_obj_tag(v___x_3674_) == 0 {
                    if leanh::lean_obj_tag(v___x_3674_) == 0 {
                        leanh::lean_dec_ref(v_a_3656_);
                        v_pos_3675_ = leanh::lean_ctor_get(v___x_3674_, 0);
                        leanh::lean_inc(v_pos_3675_);
                        v_res_3676_ = leanh::lean_ctor_get(v___x_3674_, 1);
                        leanh::lean_inc(v_res_3676_);
                        leanh::lean_dec_ref_known(v___x_3674_, 2);
                        v___x_3677_ = lean_array_push(v_acc_3655_, v_res_3676_);
                        v_acc_3655_ = v___x_3677_;
                        v_a_3656_ = v_pos_3675_;
                        state = 0;
                        continue;
                    } else {
                        v_pos_3679_ = leanh::lean_ctor_get(v___x_3674_, 0);
                        leanh::lean_inc(v_pos_3679_);
                        v_err_3680_ = leanh::lean_ctor_get(v___x_3674_, 1);
                        leanh::lean_inc(v_err_3680_);
                        leanh::lean_dec_ref_known(v___x_3674_, 2);
                        v_pos_3658_ = v_pos_3679_;
                        v_err_3659_ = v_err_3680_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_err_3681_ = leanh::lean_ctor_get(v___x_3674_, 1);
                    leanh::lean_inc(v_err_3681_);
                    leanh::lean_dec_ref_known(v___x_3674_, 2);
                    leanh::lean_inc_ref(v_a_3656_);
                    v_pos_3658_ = v_a_3656_;
                    v_err_3659_ = v_err_3681_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_idx_3660_ = leanh::lean_ctor_get(v_a_3656_, 1);
                v_isSharedCheck_3672_ = (!leanh::lean_is_exclusive(v_a_3656_)) as u8;
                if v_isSharedCheck_3672_ == 0 {
                    v_unused_3673_ = leanh::lean_ctor_get(v_a_3656_, 0);
                    leanh::lean_dec(v_unused_3673_);
                    v___x_3662_ = v_a_3656_;
                    v_isShared_3663_ = v_isSharedCheck_3672_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_3660_);
                    leanh::lean_dec(v_a_3656_);
                    v___x_3662_ = leanh::lean_box(0);
                    v_isShared_3663_ = v_isSharedCheck_3672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_idx_3664_ = leanh::lean_ctor_get(v_pos_3658_, 1);
                v___x_3665_ = lean_nat_dec_eq(v_idx_3660_, v_idx_3664_);
                leanh::lean_dec(v_idx_3660_);
                if v___x_3665_ == 0 {
                    leanh::lean_dec_ref(v_acc_3655_);
                    if v_isShared_3663_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3662_, 1);
                        leanh::lean_ctor_set(v___x_3662_, 1, v_err_3659_);
                        leanh::lean_ctor_set(v___x_3662_, 0, v_pos_3658_);
                        v___x_3667_ = v___x_3662_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3668_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_pos_3658_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_err_3659_);
                        v___x_3667_ = v_reuseFailAlloc_3668_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_err_3659_);
                    if v_isShared_3663_ == 0 {
                        leanh::lean_ctor_set(v___x_3662_, 1, v_acc_3655_);
                        leanh::lean_ctor_set(v___x_3662_, 0, v_pos_3658_);
                        v___x_3670_ = v___x_3662_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3671_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_pos_3658_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_acc_3655_);
                        v___x_3670_ = v_reuseFailAlloc_3671_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3667_;
            }
            4 => {
                return v___x_3670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(
    mut v_ident_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v_array_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: u8 = 0;
    let mut v_got_3704_: u8 = 0;
    let mut v___x_3705_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v_array_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v_got_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3773_: u8 = 0;
    let mut v_unused_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_pos_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_pos_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3790_: u8 = 0;
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut v_reuseFailAlloc_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v_unused_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v_pos_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_3688_);
                if leanh::lean_obj_tag(v___x_3689_) == 0 {
                    v_pos_3690_ = leanh::lean_ctor_get(v___x_3689_, 0);
                    v_res_3691_ = leanh::lean_ctor_get(v___x_3689_, 1);
                    v_isSharedCheck_3799_ = (!leanh::lean_is_exclusive(v___x_3689_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3693_ = v___x_3689_;
                        v_isShared_3694_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_3691_);
                        leanh::lean_inc(v_pos_3690_);
                        leanh::lean_dec(v___x_3689_);
                        v___x_3693_ = leanh::lean_box(0);
                        v_isShared_3694_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_ident_3687_);
                    v_pos_3800_ = leanh::lean_ctor_get(v___x_3689_, 0);
                    v_err_3801_ = leanh::lean_ctor_get(v___x_3689_, 1);
                    v_isSharedCheck_3808_ = (!leanh::lean_is_exclusive(v___x_3689_)) as u8;
                    if v_isSharedCheck_3808_ == 0 {
                        v___x_3803_ = v___x_3689_;
                        v_isShared_3804_ = v_isSharedCheck_3808_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3801_);
                        leanh::lean_inc(v_pos_3800_);
                        leanh::lean_dec(v___x_3689_);
                        v___x_3803_ = leanh::lean_box(0);
                        v_isShared_3804_ = v_isSharedCheck_3808_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_array_3695_ = leanh::lean_ctor_get(v_pos_3690_, 0);
                v_idx_3696_ = leanh::lean_ctor_get(v_pos_3690_, 1);
                v___x_3697_ = lean_byte_array_size(v_array_3695_);
                v___x_3698_ = lean_nat_dec_lt(v_idx_3696_, v___x_3697_);
                if v___x_3698_ == 0 {
                    leanh::lean_dec(v_res_3691_);
                    leanh::lean_dec(v_ident_3687_);
                    v___x_3699_ = leanh::lean_box(0);
                    if v_isShared_3694_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3693_, 1);
                        leanh::lean_ctor_set(v___x_3693_, 1, v___x_3699_);
                        v___x_3701_ = v___x_3693_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3702_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_pos_3690_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 1, v___x_3699_);
                        v___x_3701_ = v_reuseFailAlloc_3702_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3703_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3704_ = lean_byte_array_fget(v_array_3695_, v_idx_3696_);
                    v___x_3705_ = lean_uint8_dec_eq(v_got_3704_, v___x_3703_);
                    if v___x_3705_ == 0 {
                        leanh::lean_dec(v_res_3691_);
                        leanh::lean_dec(v_ident_3687_);
                        v___x_3706_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        if v_isShared_3694_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3693_, 1);
                            leanh::lean_ctor_set(v___x_3693_, 1, v___x_3706_);
                            v___x_3708_ = v___x_3693_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3709_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_pos_3690_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3706_);
                            v___x_3708_ = v_reuseFailAlloc_3709_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_3696_);
                        leanh::lean_inc_ref(v_array_3695_);
                        leanh::lean_del_object(v___x_3693_);
                        v_isSharedCheck_3796_ =
                            (!leanh::lean_is_exclusive(v_pos_3690_)) as u8;
                        if v_isSharedCheck_3796_ == 0 {
                            v_unused_3797_ = leanh::lean_ctor_get(v_pos_3690_, 1);
                            leanh::lean_dec(v_unused_3797_);
                            v_unused_3798_ = leanh::lean_ctor_get(v_pos_3690_, 0);
                            leanh::lean_dec(v_unused_3798_);
                            v___x_3711_ = v_pos_3690_;
                            v_isShared_3712_ = v_isSharedCheck_3796_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3690_);
                            v___x_3711_ = leanh::lean_box(0);
                            v_isShared_3712_ = v_isSharedCheck_3796_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3701_;
            }
            3 => {
                return v___x_3708_;
            }
            4 => {
                v___x_3713_ = leanh::lean_unsigned_to_nat(1);
                v___x_3714_ = lean_nat_add(v_idx_3696_, v___x_3713_);
                leanh::lean_dec(v_idx_3696_);
                if v_isShared_3712_ == 0 {
                    leanh::lean_ctor_set(v___x_3711_, 1, v___x_3714_);
                    v___x_3716_ = v___x_3711_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_array_3695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3714_);
                    v___x_3716_ = v_reuseFailAlloc_3795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3717_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_3716_);
                if leanh::lean_obj_tag(v___x_3717_) == 0 {
                    v_pos_3718_ = leanh::lean_ctor_get(v___x_3717_, 0);
                    leanh::lean_inc(v_pos_3718_);
                    v_res_3719_ = leanh::lean_ctor_get(v___x_3717_, 1);
                    leanh::lean_inc(v_res_3719_);
                    leanh::lean_dec_ref_known(v___x_3717_, 2);
                    v___x_3720_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3721_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0;
                    v___x_3722_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_3721_, v_pos_3718_);
                    if leanh::lean_obj_tag(v___x_3722_) == 0 {
                        v_pos_3723_ = leanh::lean_ctor_get(v___x_3722_, 0);
                        v_res_3724_ = leanh::lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3776_ =
                            (!leanh::lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v___x_3726_ = v___x_3722_;
                            v_isShared_3727_ = v_isSharedCheck_3776_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_3724_);
                            leanh::lean_inc(v_pos_3723_);
                            leanh::lean_dec(v___x_3722_);
                            v___x_3726_ = leanh::lean_box(0);
                            v_isShared_3727_ = v_isSharedCheck_3776_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_3719_);
                        leanh::lean_dec(v_res_3691_);
                        leanh::lean_dec(v_ident_3687_);
                        v_pos_3777_ = leanh::lean_ctor_get(v___x_3722_, 0);
                        v_err_3778_ = leanh::lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3785_ =
                            (!leanh::lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3785_ == 0 {
                            v___x_3780_ = v___x_3722_;
                            v_isShared_3781_ = v_isSharedCheck_3785_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_3778_);
                            leanh::lean_inc(v_pos_3777_);
                            leanh::lean_dec(v___x_3722_);
                            v___x_3780_ = leanh::lean_box(0);
                            v_isShared_3781_ = v_isSharedCheck_3785_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_res_3691_);
                    leanh::lean_dec(v_ident_3687_);
                    v_pos_3786_ = leanh::lean_ctor_get(v___x_3717_, 0);
                    v_err_3787_ = leanh::lean_ctor_get(v___x_3717_, 1);
                    v_isSharedCheck_3794_ = (!leanh::lean_is_exclusive(v___x_3717_)) as u8;
                    if v_isSharedCheck_3794_ == 0 {
                        v___x_3789_ = v___x_3717_;
                        v_isShared_3790_ = v_isSharedCheck_3794_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3787_);
                        leanh::lean_inc(v_pos_3786_);
                        leanh::lean_dec(v___x_3717_);
                        v___x_3789_ = leanh::lean_box(0);
                        v_isShared_3790_ = v_isSharedCheck_3794_;
                        state = 17;
                        continue;
                    }
                }
            }
            6 => {
                v_array_3728_ = leanh::lean_ctor_get(v_pos_3723_, 0);
                v_idx_3729_ = leanh::lean_ctor_get(v_pos_3723_, 1);
                v___x_3730_ = lean_byte_array_size(v_array_3728_);
                v___x_3731_ = lean_nat_dec_lt(v_idx_3729_, v___x_3730_);
                if v___x_3731_ == 0 {
                    leanh::lean_dec(v_res_3724_);
                    leanh::lean_dec(v_res_3719_);
                    leanh::lean_dec(v_res_3691_);
                    leanh::lean_dec(v_ident_3687_);
                    v___x_3732_ = leanh::lean_box(0);
                    if v_isShared_3727_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3726_, 1);
                        leanh::lean_ctor_set(v___x_3726_, 1, v___x_3732_);
                        v___x_3734_ = v___x_3726_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_pos_3723_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3732_);
                        v___x_3734_ = v_reuseFailAlloc_3735_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_3736_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v_got_3737_ = lean_byte_array_fget(v_array_3728_, v_idx_3729_);
                    v___x_3738_ = lean_uint8_dec_eq(v_got_3737_, v___x_3736_);
                    if v___x_3738_ == 0 {
                        leanh::lean_dec(v_res_3724_);
                        leanh::lean_dec(v_res_3719_);
                        leanh::lean_dec(v_res_3691_);
                        leanh::lean_dec(v_ident_3687_);
                        v___x_3739_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        if v_isShared_3727_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3726_, 1);
                            leanh::lean_ctor_set(v___x_3726_, 1, v___x_3739_);
                            v___x_3741_ = v___x_3726_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3742_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_pos_3723_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 1, v___x_3739_);
                            v___x_3741_ = v_reuseFailAlloc_3742_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_3729_);
                        leanh::lean_inc_ref(v_array_3728_);
                        v_isSharedCheck_3773_ =
                            (!leanh::lean_is_exclusive(v_pos_3723_)) as u8;
                        if v_isSharedCheck_3773_ == 0 {
                            v_unused_3774_ = leanh::lean_ctor_get(v_pos_3723_, 1);
                            leanh::lean_dec(v_unused_3774_);
                            v_unused_3775_ = leanh::lean_ctor_get(v_pos_3723_, 0);
                            leanh::lean_dec(v_unused_3775_);
                            v___x_3744_ = v_pos_3723_;
                            v_isShared_3745_ = v_isSharedCheck_3773_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3723_);
                            v___x_3744_ = leanh::lean_box(0);
                            v_isShared_3745_ = v_isSharedCheck_3773_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_3734_;
            }
            8 => {
                return v___x_3741_;
            }
            9 => {
                v___x_3746_ = lean_nat_add(v_idx_3729_, v___x_3713_);
                leanh::lean_dec(v_idx_3729_);
                if v_isShared_3745_ == 0 {
                    leanh::lean_ctor_set(v___x_3744_, 1, v___x_3746_);
                    v___x_3748_ = v___x_3744_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_array_3728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3746_);
                    v___x_3748_ = v_reuseFailAlloc_3772_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3749_ = lean_array_get_size(v_res_3691_);
                v___x_3750_ = lean_nat_dec_eq(v___x_3749_, v___x_3720_);
                if v___x_3750_ == 0 {
                    v___x_3751_ = lean_array_get_size(v_res_3724_);
                    v___x_3752_ = lean_nat_dec_eq(v___x_3751_, v___x_3720_);
                    if v___x_3752_ == 0 {
                        v___x_3753_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_3691_);
                        v___x_3754_ = leanh::lean_alloc_ctor(2, 5, (0) as u32);
                        leanh::lean_ctor_set(v___x_3754_, 0, v_ident_3687_);
                        leanh::lean_ctor_set(v___x_3754_, 1, v_res_3691_);
                        leanh::lean_ctor_set(v___x_3754_, 2, v___x_3753_);
                        leanh::lean_ctor_set(v___x_3754_, 3, v_res_3719_);
                        leanh::lean_ctor_set(v___x_3754_, 4, v_res_3724_);
                        if v_isShared_3727_ == 0 {
                            leanh::lean_ctor_set(v___x_3726_, 1, v___x_3754_);
                            leanh::lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3756_ = v___x_3726_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3757_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3757_, 1, v___x_3754_);
                            v___x_3756_ = v_reuseFailAlloc_3757_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_3724_);
                        v___x_3758_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_3758_, 0, v_ident_3687_);
                        leanh::lean_ctor_set(v___x_3758_, 1, v_res_3691_);
                        leanh::lean_ctor_set(v___x_3758_, 2, v_res_3719_);
                        if v_isShared_3727_ == 0 {
                            leanh::lean_ctor_set(v___x_3726_, 1, v___x_3758_);
                            leanh::lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3760_ = v___x_3726_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3761_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3758_);
                            v___x_3760_ = v_reuseFailAlloc_3761_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_res_3691_);
                    v___x_3762_ = lean_array_get_size(v_res_3724_);
                    leanh::lean_dec(v_res_3724_);
                    v___x_3763_ = lean_nat_dec_eq(v___x_3762_, v___x_3720_);
                    if v___x_3763_ == 0 {
                        leanh::lean_dec(v_res_3719_);
                        leanh::lean_dec(v_ident_3687_);
                        v___x_3764_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2;
                        if v_isShared_3727_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3726_, 1);
                            leanh::lean_ctor_set(v___x_3726_, 1, v___x_3764_);
                            leanh::lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3766_ = v___x_3726_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_3767_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3764_);
                            v___x_3766_ = v_reuseFailAlloc_3767_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v___x_3768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3768_, 0, v_ident_3687_);
                        leanh::lean_ctor_set(v___x_3768_, 1, v_res_3719_);
                        if v_isShared_3727_ == 0 {
                            leanh::lean_ctor_set(v___x_3726_, 1, v___x_3768_);
                            leanh::lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3770_ = v___x_3726_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3771_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3768_);
                            v___x_3770_ = v_reuseFailAlloc_3771_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            11 => {
                return v___x_3756_;
            }
            12 => {
                return v___x_3760_;
            }
            13 => {
                return v___x_3766_;
            }
            14 => {
                return v___x_3770_;
            }
            15 => {
                if v_isShared_3781_ == 0 {
                    v___x_3783_ = v___x_3780_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_pos_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_err_3778_);
                    v___x_3783_ = v_reuseFailAlloc_3784_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3783_;
            }
            17 => {
                if v_isShared_3790_ == 0 {
                    v___x_3792_ = v___x_3789_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3793_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_pos_3786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_err_3787_);
                    v___x_3792_ = v_reuseFailAlloc_3793_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3792_;
            }
            19 => {
                if v_isShared_3804_ == 0 {
                    v___x_3806_ = v___x_3803_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_pos_3800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_err_3801_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(
    mut v_a_3809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3819_: u8 = 0;
    let mut v___x_3820_: u8 = 0;
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: u8 = 0;
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u32 = 0;
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v_array_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v_got_3852_: u8 = 0;
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: u8 = 0;
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut v_unused_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_reuseFailAlloc_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_unused_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3813_ = leanh::lean_ctor_get(v_a_3809_, 0);
                v_idx_3814_ = leanh::lean_ctor_get(v_a_3809_, 1);
                v___x_3815_ = lean_byte_array_size(v_array_3813_);
                v___x_3816_ = lean_nat_dec_lt(v_idx_3814_, v___x_3815_);
                if v___x_3816_ == 0 {
                    v___x_3817_ = leanh::lean_box(0);
                    v___x_3818_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3818_, 0, v_a_3809_);
                    leanh::lean_ctor_set(v___x_3818_, 1, v___x_3817_);
                    return v___x_3818_;
                } else {
                    v_c_3819_ = lean_byte_array_fget(v_array_3813_, v_idx_3814_);
                    v___x_3820_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
                    );
                    v___x_3821_ = lean_uint8_dec_le(v___x_3820_, v_c_3819_);
                    if v___x_3821_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_3822_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3,
                        );
                        v___x_3823_ = lean_uint8_dec_le(v_c_3819_, v___x_3822_);
                        if v___x_3823_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_idx_3814_);
                            leanh::lean_inc_ref(v_array_3813_);
                            v_isSharedCheck_3884_ =
                                (!leanh::lean_is_exclusive(v_a_3809_)) as u8;
                            if v_isSharedCheck_3884_ == 0 {
                                v_unused_3885_ = leanh::lean_ctor_get(v_a_3809_, 1);
                                leanh::lean_dec(v_unused_3885_);
                                v_unused_3886_ = leanh::lean_ctor_get(v_a_3809_, 0);
                                leanh::lean_dec(v_unused_3886_);
                                v___x_3825_ = v_a_3809_;
                                v_isShared_3826_ = v_isSharedCheck_3884_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_3809_);
                                v___x_3825_ = leanh::lean_box(0);
                                v_isShared_3826_ = v_isSharedCheck_3884_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3811_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3812_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3812_, 0, v_a_3809_);
                leanh::lean_ctor_set(v___x_3812_, 1, v___x_3811_);
                return v___x_3812_;
            }
            2 => {
                v___x_3827_ = leanh::lean_unsigned_to_nat(1);
                v___x_3828_ = lean_nat_add(v_idx_3814_, v___x_3827_);
                leanh::lean_dec(v_idx_3814_);
                if v_isShared_3826_ == 0 {
                    leanh::lean_ctor_set(v___x_3825_, 1, v___x_3828_);
                    v_it_x27_3830_ = v___x_3825_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_array_3813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___x_3828_);
                    v_it_x27_3830_ = v_reuseFailAlloc_3883_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3831_ = lean_uint8_to_uint32(v_c_3819_);
                v___x_3832_ = lean_uint32_to_uint8(v___x_3831_);
                v___x_3833_ = lean_uint8_sub(v___x_3832_, v___x_3820_);
                v___x_3834_ = lean_uint8_to_nat(v___x_3833_);
                v___x_3835_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3830_, v___x_3834_);
                v_fst_3836_ = leanh::lean_ctor_get(v___x_3835_, 0);
                v_snd_3837_ = leanh::lean_ctor_get(v___x_3835_, 1);
                v_isSharedCheck_3882_ = (!leanh::lean_is_exclusive(v___x_3835_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v___x_3839_ = v___x_3835_;
                    v_isShared_3840_ = v_isSharedCheck_3882_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3837_);
                    leanh::lean_inc(v_fst_3836_);
                    leanh::lean_dec(v___x_3835_);
                    v___x_3839_ = leanh::lean_box(0);
                    v_isShared_3840_ = v_isSharedCheck_3882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3841_ = leanh::lean_unsigned_to_nat(0);
                v___x_3842_ = lean_nat_dec_eq(v_fst_3836_, v___x_3841_);
                if v___x_3842_ == 0 {
                    v_array_3843_ = leanh::lean_ctor_get(v_snd_3837_, 0);
                    v_idx_3844_ = leanh::lean_ctor_get(v_snd_3837_, 1);
                    v___x_3845_ = lean_byte_array_size(v_array_3843_);
                    v___x_3846_ = lean_nat_dec_lt(v_idx_3844_, v___x_3845_);
                    if v___x_3846_ == 0 {
                        leanh::lean_dec(v_fst_3836_);
                        v___x_3847_ = leanh::lean_box(0);
                        if v_isShared_3840_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3839_, 1);
                            leanh::lean_ctor_set(v___x_3839_, 1, v___x_3847_);
                            leanh::lean_ctor_set(v___x_3839_, 0, v_snd_3837_);
                            v___x_3849_ = v___x_3839_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3850_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_snd_3837_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 1, v___x_3847_);
                            v___x_3849_ = v_reuseFailAlloc_3850_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_3851_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                        v_got_3852_ = lean_byte_array_fget(v_array_3843_, v_idx_3844_);
                        v___x_3853_ = lean_uint8_dec_eq(v_got_3852_, v___x_3851_);
                        if v___x_3853_ == 0 {
                            leanh::lean_dec(v_fst_3836_);
                            v___x_3854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                            if v_isShared_3840_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3839_, 1);
                                leanh::lean_ctor_set(v___x_3839_, 1, v___x_3854_);
                                leanh::lean_ctor_set(v___x_3839_, 0, v_snd_3837_);
                                v___x_3856_ = v___x_3839_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3857_ =
                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_snd_3837_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3854_);
                                v___x_3856_ = v_reuseFailAlloc_3857_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v_idx_3844_);
                            leanh::lean_inc_ref(v_array_3843_);
                            v_isSharedCheck_3875_ =
                                (!leanh::lean_is_exclusive(v_snd_3837_)) as u8;
                            if v_isSharedCheck_3875_ == 0 {
                                v_unused_3876_ = leanh::lean_ctor_get(v_snd_3837_, 1);
                                leanh::lean_dec(v_unused_3876_);
                                v_unused_3877_ = leanh::lean_ctor_get(v_snd_3837_, 0);
                                leanh::lean_dec(v_unused_3877_);
                                v___x_3859_ = v_snd_3837_;
                                v_isShared_3860_ = v_isSharedCheck_3875_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v_snd_3837_);
                                v___x_3859_ = leanh::lean_box(0);
                                v_isShared_3860_ = v_isSharedCheck_3875_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_3836_);
                    v___x_3878_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3840_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3839_, 1);
                        leanh::lean_ctor_set(v___x_3839_, 1, v___x_3878_);
                        leanh::lean_ctor_set(v___x_3839_, 0, v_snd_3837_);
                        v___x_3880_ = v___x_3839_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3881_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_snd_3837_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3878_);
                        v___x_3880_ = v_reuseFailAlloc_3881_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3849_;
            }
            6 => {
                return v___x_3856_;
            }
            7 => {
                v___x_3861_ = lean_nat_add(v_idx_3844_, v___x_3827_);
                leanh::lean_dec(v_idx_3844_);
                leanh::lean_inc(v___x_3861_);
                leanh::lean_inc_ref(v_array_3843_);
                if v_isShared_3860_ == 0 {
                    leanh::lean_ctor_set(v___x_3859_, 1, v___x_3861_);
                    v___x_3863_ = v___x_3859_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_array_3843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3861_);
                    v___x_3863_ = v_reuseFailAlloc_3874_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3864_ = lean_nat_dec_lt(v___x_3861_, v___x_3845_);
                if v___x_3864_ == 0 {
                    leanh::lean_dec(v___x_3861_);
                    leanh::lean_dec_ref(v_array_3843_);
                    leanh::lean_dec(v_fst_3836_);
                    v___x_3865_ = leanh::lean_box(0);
                    if v_isShared_3840_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3839_, 1);
                        leanh::lean_ctor_set(v___x_3839_, 1, v___x_3865_);
                        leanh::lean_ctor_set(v___x_3839_, 0, v___x_3863_);
                        v___x_3867_ = v___x_3839_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3868_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3863_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3865_);
                        v___x_3867_ = v_reuseFailAlloc_3868_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3839_);
                    v___x_3869_ = lean_byte_array_fget(v_array_3843_, v___x_3861_);
                    leanh::lean_dec(v___x_3861_);
                    leanh::lean_dec_ref(v_array_3843_);
                    v___x_3870_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0,
                    );
                    v___x_3871_ = lean_uint8_dec_eq(v___x_3869_, v___x_3870_);
                    if v___x_3871_ == 0 {
                        v___x_3872_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(
                            v_fst_3836_,
                            v___x_3863_,
                        );
                        return v___x_3872_;
                    } else {
                        leanh::lean_dec(v_fst_3836_);
                        v___x_3873_ =
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_3863_);
                        return v___x_3873_;
                    }
                }
            }
            9 => {
                return v___x_3867_;
            }
            10 => {
                return v___x_3880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2()
-> u8 {
    let mut v___x_3890_: u32 = 0;
    let mut v___x_3891_: u8 = 0;
    v___x_3890_ = 13;
    v___x_3891_ = lean_uint32_to_uint8(v___x_3890_);
    return v___x_3891_;
}
pub unsafe fn _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3()
-> u8 {
    let mut v___x_3892_: u32 = 0;
    let mut v___x_3893_: u8 = 0;
    v___x_3892_ = 99;
    v___x_3893_ = lean_uint32_to_uint8(v___x_3892_);
    return v___x_3893_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(
    mut v___x_3894_: u8,
    mut v_acc_3895_: *mut leanh::LeanObject,
    mut v_a_3896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u8 = 0;
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3911_: u8 = 0;
    let mut v___x_3912_: u8 = 0;
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: u8 = 0;
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3897_ = leanh::lean_ctor_get(v_a_3896_, 0);
                v_idx_3898_ = leanh::lean_ctor_get(v_a_3896_, 1);
                leanh::lean_inc(v_idx_3898_);
                v___x_3908_ = lean_byte_array_size(v_array_3897_);
                v___x_3909_ = lean_nat_dec_lt(v_idx_3898_, v___x_3908_);
                if v___x_3909_ == 0 {
                    v___x_3910_ = leanh::lean_box(0);
                    leanh::lean_inc(v_idx_3898_);
                    v_pos_3900_ = v_a_3896_;
                    v_idx_3901_ = v_idx_3898_;
                    v_err_3902_ = v___x_3910_;
                    state = 1;
                    continue;
                } else {
                    v_c_3911_ = lean_byte_array_fget(v_array_3897_, v_idx_3898_);
                    v___x_3912_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2,
                    );
                    v___x_3913_ = lean_uint8_dec_eq(v_c_3911_, v___x_3912_);
                    if v___x_3913_ == 0 {
                        v___x_3914_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3915_ = lean_nat_add(v_idx_3898_, v___x_3914_);
                        leanh::lean_inc_ref(v_array_3897_);
                        v_it_x27_3916_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_it_x27_3916_, 0, v_array_3897_);
                        leanh::lean_ctor_set(v_it_x27_3916_, 1, v___x_3915_);
                        v___x_3922_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2), core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once), _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2);
                        v___x_3923_ = lean_uint8_dec_eq(v_c_3911_, v___x_3922_);
                        if v___x_3923_ == 0 {
                            v___x_3924_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once), _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
                            v___x_3925_ = lean_uint8_dec_eq(v___x_3894_, v___x_3924_);
                            v___y_3918_ = v___x_3925_;
                            state = 3;
                            continue;
                        } else {
                            v___y_3918_ = v___x_3913_;
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3903_ = lean_nat_dec_eq(v_idx_3898_, v_idx_3901_);
                leanh::lean_dec(v_idx_3901_);
                leanh::lean_dec(v_idx_3898_);
                if v___x_3903_ == 0 {
                    leanh::lean_dec_ref(v_acc_3895_);
                    leanh::lean_inc(v_err_3902_);
                    v___x_3904_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3904_, 0, v_pos_3900_);
                    leanh::lean_ctor_set(v___x_3904_, 1, v_err_3902_);
                    return v___x_3904_;
                } else {
                    v___x_3905_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3905_, 0, v_pos_3900_);
                    leanh::lean_ctor_set(v___x_3905_, 1, v_acc_3895_);
                    return v___x_3905_;
                }
            }
            2 => {
                v___x_3907_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1;
                leanh::lean_inc(v_idx_3898_);
                v_pos_3900_ = v_a_3896_;
                v_idx_3901_ = v_idx_3898_;
                v_err_3902_ = v___x_3907_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_3918_ == 0 {
                    leanh::lean_dec_ref_known(v_it_x27_3916_, 2);
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_idx_3898_);
                    leanh::lean_dec_ref(v_a_3896_);
                    v___x_3919_ = leanh::lean_box((v_c_3911_) as usize);
                    v___x_3920_ = lean_array_push(v_acc_3895_, v___x_3919_);
                    v_acc_3895_ = v___x_3920_;
                    v_a_3896_ = v_it_x27_3916_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___boxed(
    mut v___x_3926_: *mut leanh::LeanObject,
    mut v_acc_3927_: *mut leanh::LeanObject,
    mut v_a_3928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2518__boxed_3929_: u8 = 0;
    let mut v_res_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2518__boxed_3929_ = (leanh::lean_unbox(v___x_3926_) as u8);
    v_res_3930_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_2518__boxed_3929_, v_acc_3927_, v_a_3928_);
    return v_res_3930_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(
    mut v_actions_3933_: *mut leanh::LeanObject,
    mut v_a_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: u8 = 0;
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3954_: u8 = 0;
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_array_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: u8 = 0;
    let mut v___x_3967_: u8 = 0;
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v_pos_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_array_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v_utf8_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    let mut v_got_4016_: u8 = 0;
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_unused_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4031_: u8 = 0;
    let mut v_pos_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4040_: u8 = 0;
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v_array_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v_utf8_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u8 = 0;
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: u8 = 0;
    let mut v_got_4064_: u8 = 0;
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4078_: u8 = 0;
    let mut v_unused_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4087_: u8 = 0;
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3959_ = leanh::lean_ctor_get(v_a_3934_, 0);
                v_idx_3960_ = leanh::lean_ctor_get(v_a_3934_, 1);
                v___x_3961_ = lean_byte_array_size(v_array_3959_);
                v___x_3962_ = lean_nat_dec_lt(v_idx_3960_, v___x_3961_);
                if v___x_3962_ == 0 {
                    leanh::lean_dec_ref(v_actions_3933_);
                    v___x_3963_ = leanh::lean_box(0);
                    v___x_3964_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3964_, 0, v_a_3934_);
                    leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                    return v___x_3964_;
                } else {
                    v___x_3965_ = lean_byte_array_fget(v_array_3959_, v_idx_3960_);
                    v___x_3966_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once), _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
                    v___x_3967_ = lean_uint8_dec_eq(v___x_3965_, v___x_3966_);
                    if v___x_3967_ == 0 {
                        v___x_3968_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_3934_);
                        if leanh::lean_obj_tag(v___x_3968_) == 0 {
                            v_pos_3969_ = leanh::lean_ctor_get(v___x_3968_, 0);
                            v_res_3970_ = leanh::lean_ctor_get(v___x_3968_, 1);
                            v_isSharedCheck_4031_ =
                                (!leanh::lean_is_exclusive(v___x_3968_)) as u8;
                            if v_isSharedCheck_4031_ == 0 {
                                v___x_3972_ = v___x_3968_;
                                v_isShared_3973_ = v_isSharedCheck_4031_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_res_3970_);
                                leanh::lean_inc(v_pos_3969_);
                                leanh::lean_dec(v___x_3968_);
                                v___x_3972_ = leanh::lean_box(0);
                                v_isShared_3973_ = v_isSharedCheck_4031_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_actions_3933_);
                            v_pos_4032_ = leanh::lean_ctor_get(v___x_3968_, 0);
                            v_err_4033_ = leanh::lean_ctor_get(v___x_3968_, 1);
                            v_isSharedCheck_4040_ =
                                (!leanh::lean_is_exclusive(v___x_3968_)) as u8;
                            if v_isSharedCheck_4040_ == 0 {
                                v___x_4035_ = v___x_3968_;
                                v_isShared_4036_ = v_isSharedCheck_4040_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_4033_);
                                leanh::lean_inc(v_pos_4032_);
                                leanh::lean_dec(v___x_3968_);
                                v___x_4035_ = leanh::lean_box(0);
                                v_isShared_4036_ = v_isSharedCheck_4040_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        v___x_4041_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0;
                        v___x_4042_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_3965_, v___x_4041_, v_a_3934_);
                        if leanh::lean_obj_tag(v___x_4042_) == 0 {
                            v_pos_4043_ = leanh::lean_ctor_get(v___x_4042_, 0);
                            v_isSharedCheck_4081_ =
                                (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4081_ == 0 {
                                v_unused_4082_ = leanh::lean_ctor_get(v___x_4042_, 1);
                                leanh::lean_dec(v_unused_4082_);
                                v___x_4045_ = v___x_4042_;
                                v_isShared_4046_ = v_isSharedCheck_4081_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_pos_4043_);
                                leanh::lean_dec(v___x_4042_);
                                v___x_4045_ = leanh::lean_box(0);
                                v_isShared_4046_ = v_isSharedCheck_4081_;
                                state = 18;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_actions_3933_);
                            v_pos_4083_ = leanh::lean_ctor_get(v___x_4042_, 0);
                            v_err_4084_ = leanh::lean_ctor_get(v___x_4042_, 1);
                            v_isSharedCheck_4091_ =
                                (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4091_ == 0 {
                                v___x_4086_ = v___x_4042_;
                                v_isShared_4087_ = v_isSharedCheck_4091_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_4084_);
                                leanh::lean_inc(v_pos_4083_);
                                leanh::lean_dec(v___x_4042_);
                                v___x_4086_ = leanh::lean_box(0);
                                v_isShared_4087_ = v_isSharedCheck_4091_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3939_ = lean_byte_array_size(v_array_3937_);
                leanh::lean_dec_ref(v_array_3937_);
                v___x_3940_ = lean_nat_dec_lt(v_idx_3938_, v___x_3939_);
                leanh::lean_dec(v_idx_3938_);
                if v___x_3940_ == 0 {
                    v___x_3941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3941_, 0, v_pos_3936_);
                    leanh::lean_ctor_set(v___x_3941_, 1, v_actions_3933_);
                    return v___x_3941_;
                } else {
                    v_a_3934_ = v_pos_3936_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_array_3945_ = leanh::lean_ctor_get(v_pos_3944_, 0);
                leanh::lean_inc_ref(v_array_3945_);
                v_idx_3946_ = leanh::lean_ctor_get(v_pos_3944_, 1);
                leanh::lean_inc(v_idx_3946_);
                v_pos_3936_ = v_pos_3944_;
                v_array_3937_ = v_array_3945_;
                v_idx_3938_ = v_idx_3946_;
                state = 1;
                continue;
            }
            3 => {
                if leanh::lean_obj_tag(v___y_3948_) == 0 {
                    v_pos_3949_ = leanh::lean_ctor_get(v___y_3948_, 0);
                    leanh::lean_inc(v_pos_3949_);
                    leanh::lean_dec_ref_known(v___y_3948_, 2);
                    v_pos_3944_ = v_pos_3949_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_actions_3933_);
                    v_pos_3950_ = leanh::lean_ctor_get(v___y_3948_, 0);
                    v_err_3951_ = leanh::lean_ctor_get(v___y_3948_, 1);
                    v_isSharedCheck_3958_ = (!leanh::lean_is_exclusive(v___y_3948_)) as u8;
                    if v_isSharedCheck_3958_ == 0 {
                        v___x_3953_ = v___y_3948_;
                        v_isShared_3954_ = v_isSharedCheck_3958_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3951_);
                        leanh::lean_inc(v_pos_3950_);
                        leanh::lean_dec(v___y_3948_);
                        v___x_3953_ = leanh::lean_box(0);
                        v_isShared_3954_ = v_isSharedCheck_3958_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3954_ == 0 {
                    v___x_3956_ = v___x_3953_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_pos_3950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_err_3951_);
                    v___x_3956_ = v_reuseFailAlloc_3957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3956_;
            }
            6 => {
                v_array_4001_ = leanh::lean_ctor_get(v_pos_3969_, 0);
                v_idx_4002_ = leanh::lean_ctor_get(v_pos_3969_, 1);
                leanh::lean_inc(v_idx_4002_);
                v___x_4011_ = lean_byte_array_size(v_array_4001_);
                v___x_4012_ = lean_nat_dec_lt(v_idx_4002_, v___x_4011_);
                if v___x_4012_ == 0 {
                    v___x_4013_ = leanh::lean_box(0);
                    leanh::lean_inc(v_pos_3969_);
                    v___x_4014_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4014_, 0, v_pos_3969_);
                    leanh::lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                    leanh::lean_inc(v_idx_4002_);
                    v___y_4004_ = v___x_4014_;
                    v_pos_4005_ = v_pos_3969_;
                    v_idx_4006_ = v_idx_4002_;
                    state = 13;
                    continue;
                } else {
                    v___x_4015_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2,
                    );
                    v_got_4016_ = lean_byte_array_fget(v_array_4001_, v_idx_4002_);
                    v___x_4017_ = lean_uint8_dec_eq(v_got_4016_, v___x_4015_);
                    if v___x_4017_ == 0 {
                        v___x_4018_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9,
                        );
                        leanh::lean_inc(v_pos_3969_);
                        v___x_4019_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4019_, 0, v_pos_3969_);
                        leanh::lean_ctor_set(v___x_4019_, 1, v___x_4018_);
                        leanh::lean_inc(v_idx_4002_);
                        v___y_4004_ = v___x_4019_;
                        v_pos_4005_ = v_pos_3969_;
                        v_idx_4006_ = v_idx_4002_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_array_4001_);
                        v_isSharedCheck_4028_ =
                            (!leanh::lean_is_exclusive(v_pos_3969_)) as u8;
                        if v_isSharedCheck_4028_ == 0 {
                            v_unused_4029_ = leanh::lean_ctor_get(v_pos_3969_, 1);
                            leanh::lean_dec(v_unused_4029_);
                            v_unused_4030_ = leanh::lean_ctor_get(v_pos_3969_, 0);
                            leanh::lean_dec(v_unused_4030_);
                            v___x_4021_ = v_pos_3969_;
                            v_isShared_4022_ = v_isSharedCheck_4028_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_3969_);
                            v___x_4021_ = leanh::lean_box(0);
                            v_isShared_4022_ = v_isSharedCheck_4028_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_3978_ = lean_array_push(v_actions_3933_, v_res_3970_);
                v___x_3979_ = lean_byte_array_size(v_array_3976_);
                leanh::lean_dec_ref(v_array_3976_);
                v___x_3980_ = lean_nat_dec_lt(v_idx_3977_, v___x_3979_);
                leanh::lean_dec(v_idx_3977_);
                if v___x_3980_ == 0 {
                    if v_isShared_3973_ == 0 {
                        leanh::lean_ctor_set(v___x_3972_, 1, v___x_3978_);
                        leanh::lean_ctor_set(v___x_3972_, 0, v_pos_3975_);
                        v___x_3982_ = v___x_3972_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3983_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_pos_3975_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3978_);
                        v___x_3982_ = v_reuseFailAlloc_3983_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3972_);
                    v_actions_3933_ = v___x_3978_;
                    v_a_3934_ = v_pos_3975_;
                    state = 0;
                    continue;
                }
            }
            8 => {
                return v___x_3982_;
            }
            9 => {
                v_array_3987_ = leanh::lean_ctor_get(v_pos_3986_, 0);
                leanh::lean_inc_ref(v_array_3987_);
                v_idx_3988_ = leanh::lean_ctor_get(v_pos_3986_, 1);
                leanh::lean_inc(v_idx_3988_);
                v_pos_3975_ = v_pos_3986_;
                v_array_3976_ = v_array_3987_;
                v_idx_3977_ = v_idx_3988_;
                state = 7;
                continue;
            }
            10 => {
                if leanh::lean_obj_tag(v___y_3990_) == 0 {
                    v_pos_3991_ = leanh::lean_ctor_get(v___y_3990_, 0);
                    leanh::lean_inc(v_pos_3991_);
                    leanh::lean_dec_ref_known(v___y_3990_, 2);
                    v_pos_3986_ = v_pos_3991_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_3972_);
                    leanh::lean_dec(v_res_3970_);
                    leanh::lean_dec_ref(v_actions_3933_);
                    v_pos_3992_ = leanh::lean_ctor_get(v___y_3990_, 0);
                    v_err_3993_ = leanh::lean_ctor_get(v___y_3990_, 1);
                    v_isSharedCheck_4000_ = (!leanh::lean_is_exclusive(v___y_3990_)) as u8;
                    if v_isSharedCheck_4000_ == 0 {
                        v___x_3995_ = v___y_3990_;
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_3993_);
                        leanh::lean_inc(v_pos_3992_);
                        leanh::lean_dec(v___y_3990_);
                        v___x_3995_ = leanh::lean_box(0);
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_3996_ == 0 {
                    v___x_3998_ = v___x_3995_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_pos_3992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_err_3993_);
                    v___x_3998_ = v_reuseFailAlloc_3999_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3998_;
            }
            13 => {
                v___x_4007_ = lean_nat_dec_eq(v_idx_4002_, v_idx_4006_);
                leanh::lean_dec(v_idx_4006_);
                leanh::lean_dec(v_idx_4002_);
                if v___x_4007_ == 0 {
                    leanh::lean_dec_ref(v_pos_4005_);
                    v___y_3990_ = v___y_4004_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4004_);
                    v_utf8_4008_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1,
                    );
                    v___x_4009_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_4008_, v_pos_4005_);
                    if leanh::lean_obj_tag(v___x_4009_) == 0 {
                        v_pos_4010_ = leanh::lean_ctor_get(v___x_4009_, 0);
                        leanh::lean_inc(v_pos_4010_);
                        leanh::lean_dec_ref_known(v___x_4009_, 2);
                        v_pos_3986_ = v_pos_4010_;
                        state = 9;
                        continue;
                    } else {
                        v___y_3990_ = v___x_4009_;
                        state = 10;
                        continue;
                    }
                }
            }
            14 => {
                v___x_4023_ = leanh::lean_unsigned_to_nat(1);
                v___x_4024_ = lean_nat_add(v_idx_4002_, v___x_4023_);
                leanh::lean_dec(v_idx_4002_);
                leanh::lean_inc(v___x_4024_);
                leanh::lean_inc_ref(v_array_4001_);
                if v_isShared_4022_ == 0 {
                    leanh::lean_ctor_set(v___x_4021_, 1, v___x_4024_);
                    v___x_4026_ = v___x_4021_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_array_4001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4024_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_pos_3975_ = v___x_4026_;
                v_array_3976_ = v_array_4001_;
                v_idx_3977_ = v___x_4024_;
                state = 7;
                continue;
            }
            16 => {
                if v_isShared_4036_ == 0 {
                    v___x_4038_ = v___x_4035_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_pos_4032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_err_4033_);
                    v___x_4038_ = v_reuseFailAlloc_4039_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4038_;
            }
            18 => {
                v_array_4047_ = leanh::lean_ctor_get(v_pos_4043_, 0);
                v_idx_4048_ = leanh::lean_ctor_get(v_pos_4043_, 1);
                leanh::lean_inc(v_idx_4048_);
                v___x_4057_ = lean_byte_array_size(v_array_4047_);
                v___x_4058_ = lean_nat_dec_lt(v_idx_4048_, v___x_4057_);
                if v___x_4058_ == 0 {
                    v___x_4059_ = leanh::lean_box(0);
                    leanh::lean_inc(v_pos_4043_);
                    if v_isShared_4046_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4045_, 1);
                        leanh::lean_ctor_set(v___x_4045_, 1, v___x_4059_);
                        v___x_4061_ = v___x_4045_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_4062_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_pos_4043_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4059_);
                        v___x_4061_ = v_reuseFailAlloc_4062_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_4063_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2,
                    );
                    v_got_4064_ = lean_byte_array_fget(v_array_4047_, v_idx_4048_);
                    v___x_4065_ = lean_uint8_dec_eq(v_got_4064_, v___x_4063_);
                    if v___x_4065_ == 0 {
                        v___x_4066_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9,
                        );
                        leanh::lean_inc(v_pos_4043_);
                        if v_isShared_4046_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4045_, 1);
                            leanh::lean_ctor_set(v___x_4045_, 1, v___x_4066_);
                            v___x_4068_ = v___x_4045_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_4069_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_pos_4043_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4066_);
                            v___x_4068_ = v_reuseFailAlloc_4069_;
                            state = 21;
                            continue;
                        }
                    } else {
                        leanh::lean_inc_ref(v_array_4047_);
                        leanh::lean_del_object(v___x_4045_);
                        v_isSharedCheck_4078_ =
                            (!leanh::lean_is_exclusive(v_pos_4043_)) as u8;
                        if v_isSharedCheck_4078_ == 0 {
                            v_unused_4079_ = leanh::lean_ctor_get(v_pos_4043_, 1);
                            leanh::lean_dec(v_unused_4079_);
                            v_unused_4080_ = leanh::lean_ctor_get(v_pos_4043_, 0);
                            leanh::lean_dec(v_unused_4080_);
                            v___x_4071_ = v_pos_4043_;
                            v_isShared_4072_ = v_isSharedCheck_4078_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_4043_);
                            v___x_4071_ = leanh::lean_box(0);
                            v_isShared_4072_ = v_isSharedCheck_4078_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            19 => {
                v___x_4053_ = lean_nat_dec_eq(v_idx_4048_, v_idx_4052_);
                leanh::lean_dec(v_idx_4052_);
                leanh::lean_dec(v_idx_4048_);
                if v___x_4053_ == 0 {
                    leanh::lean_dec_ref(v_pos_4051_);
                    v___y_3948_ = v___y_4050_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_4050_);
                    v_utf8_4054_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1,
                    );
                    v___x_4055_ =
                        l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_4054_, v_pos_4051_);
                    if leanh::lean_obj_tag(v___x_4055_) == 0 {
                        v_pos_4056_ = leanh::lean_ctor_get(v___x_4055_, 0);
                        leanh::lean_inc(v_pos_4056_);
                        leanh::lean_dec_ref_known(v___x_4055_, 2);
                        v_pos_3944_ = v_pos_4056_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3948_ = v___x_4055_;
                        state = 3;
                        continue;
                    }
                }
            }
            20 => {
                leanh::lean_inc(v_idx_4048_);
                v___y_4050_ = v___x_4061_;
                v_pos_4051_ = v_pos_4043_;
                v_idx_4052_ = v_idx_4048_;
                state = 19;
                continue;
            }
            21 => {
                leanh::lean_inc(v_idx_4048_);
                v___y_4050_ = v___x_4068_;
                v_pos_4051_ = v_pos_4043_;
                v_idx_4052_ = v_idx_4048_;
                state = 19;
                continue;
            }
            22 => {
                v___x_4073_ = leanh::lean_unsigned_to_nat(1);
                v___x_4074_ = lean_nat_add(v_idx_4048_, v___x_4073_);
                leanh::lean_dec(v_idx_4048_);
                leanh::lean_inc(v___x_4074_);
                leanh::lean_inc_ref(v_array_4047_);
                if v_isShared_4072_ == 0 {
                    leanh::lean_ctor_set(v___x_4071_, 1, v___x_4074_);
                    v___x_4076_ = v___x_4071_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4077_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_array_4047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4074_);
                    v___x_4076_ = v_reuseFailAlloc_4077_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v_pos_3936_ = v___x_4076_;
                v_array_3937_ = v_array_4047_;
                v_idx_3938_ = v___x_4074_;
                state = 1;
                continue;
            }
            24 => {
                if v_isShared_4087_ == 0 {
                    v___x_4089_ = v___x_4086_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_pos_4083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_err_4084_);
                    v___x_4089_ = v_reuseFailAlloc_4090_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(
    mut v_a_4094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0;
    v___x_4096_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_4095_, v_a_4094_);
    return v___x_4096_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4097_ = leanh::lean_unsigned_to_nat(0);
    v___x_4098_ = l_Nat_reprFast(v___x_4097_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4099_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0,
    );
    v___x_4100_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_4101_ = lean_string_append(v___x_4100_, v___x_4099_);
    return v___x_4101_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4102_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_4103_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1,
    );
    v___x_4104_ = lean_string_append(v___x_4103_, v___x_4102_);
    return v___x_4104_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2,
    );
    v___x_4106_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4106_, 0, v___x_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(
    mut v_a_4107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: u8 = 0;
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: u8 = 0;
    let mut v_got_4115_: u8 = 0;
    let mut v___x_4116_: u8 = 0;
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_unused_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4108_ = leanh::lean_ctor_get(v_a_4107_, 0);
                v_idx_4109_ = leanh::lean_ctor_get(v_a_4107_, 1);
                v___x_4110_ = lean_byte_array_size(v_array_4108_);
                v___x_4111_ = lean_nat_dec_lt(v_idx_4109_, v___x_4110_);
                if v___x_4111_ == 0 {
                    v___x_4112_ = leanh::lean_box(0);
                    v___x_4113_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4113_, 0, v_a_4107_);
                    leanh::lean_ctor_set(v___x_4113_, 1, v___x_4112_);
                    return v___x_4113_;
                } else {
                    v___x_4114_ = 0;
                    v_got_4115_ = lean_byte_array_fget(v_array_4108_, v_idx_4109_);
                    v___x_4116_ = lean_uint8_dec_eq(v_got_4115_, v___x_4114_);
                    if v___x_4116_ == 0 {
                        v___x_4117_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        v___x_4118_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4118_, 0, v_a_4107_);
                        leanh::lean_ctor_set(v___x_4118_, 1, v___x_4117_);
                        return v___x_4118_;
                    } else {
                        leanh::lean_inc(v_idx_4109_);
                        leanh::lean_inc_ref(v_array_4108_);
                        v_isSharedCheck_4129_ = (!leanh::lean_is_exclusive(v_a_4107_)) as u8;
                        if v_isSharedCheck_4129_ == 0 {
                            v_unused_4130_ = leanh::lean_ctor_get(v_a_4107_, 1);
                            leanh::lean_dec(v_unused_4130_);
                            v_unused_4131_ = leanh::lean_ctor_get(v_a_4107_, 0);
                            leanh::lean_dec(v_unused_4131_);
                            v___x_4120_ = v_a_4107_;
                            v_isShared_4121_ = v_isSharedCheck_4129_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_4107_);
                            v___x_4120_ = leanh::lean_box(0);
                            v_isShared_4121_ = v_isSharedCheck_4129_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4122_ = leanh::lean_unsigned_to_nat(1);
                v___x_4123_ = lean_nat_add(v_idx_4109_, v___x_4122_);
                leanh::lean_dec(v_idx_4109_);
                if v_isShared_4121_ == 0 {
                    leanh::lean_ctor_set(v___x_4120_, 1, v___x_4123_);
                    v___x_4125_ = v___x_4120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_array_4108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 1, v___x_4123_);
                    v___x_4125_ = v_reuseFailAlloc_4128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4126_ = leanh::lean_box(0);
                v___x_4127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4127_, 0, v___x_4125_);
                leanh::lean_ctor_set(v___x_4127_, 1, v___x_4126_);
                return v___x_4127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4()
-> u8 {
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: u8 = 0;
    v___x_4138_ = 15;
    v___x_4139_ = lean_uint8_complement(v___x_4138_);
    return v___x_4139_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(
    mut v_uidx_4140_: u64,
    mut v_shift_4141_: u64,
    mut v_a_4142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v_c_4152_: u8 = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4158_: u64 = 0;
    let mut v___y_4159_: u8 = 0;
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: u8 = 0;
    let mut v___x_4172_: u64 = 0;
    let mut v___x_4173_: u64 = 0;
    let mut v___x_4174_: u64 = 0;
    let mut v___x_4175_: u8 = 0;
    let mut v___x_4176_: u8 = 0;
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4178_: u64 = 0;
    let mut v___x_4179_: u64 = 0;
    let mut v___x_4181_: u64 = 0;
    let mut v___x_4182_: u64 = 0;
    let mut v___x_4183_: u64 = 0;
    let mut v___x_4184_: u64 = 0;
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: u8 = 0;
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: u64 = 0;
    let mut v___x_4193_: u8 = 0;
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: u8 = 0;
    let mut v___x_4196_: u8 = 0;
    let mut v___x_4197_: u8 = 0;
    let mut v_reuseFailAlloc_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_unused_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4143_ = leanh::lean_ctor_get(v_a_4142_, 0);
                v_idx_4144_ = leanh::lean_ctor_get(v_a_4142_, 1);
                v___x_4145_ = lean_byte_array_size(v_array_4143_);
                v___x_4146_ = lean_nat_dec_lt(v_idx_4144_, v___x_4145_);
                if v___x_4146_ == 0 {
                    v___x_4147_ = leanh::lean_box(0);
                    v___x_4148_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4148_, 0, v_a_4142_);
                    leanh::lean_ctor_set(v___x_4148_, 1, v___x_4147_);
                    return v___x_4148_;
                } else {
                    leanh::lean_inc(v_idx_4144_);
                    leanh::lean_inc_ref(v_array_4143_);
                    v_isSharedCheck_4199_ = (!leanh::lean_is_exclusive(v_a_4142_)) as u8;
                    if v_isSharedCheck_4199_ == 0 {
                        v_unused_4200_ = leanh::lean_ctor_get(v_a_4142_, 1);
                        leanh::lean_dec(v_unused_4200_);
                        v_unused_4201_ = leanh::lean_ctor_get(v_a_4142_, 0);
                        leanh::lean_dec(v_unused_4201_);
                        v___x_4150_ = v_a_4142_;
                        v_isShared_4151_ = v_isSharedCheck_4199_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_4142_);
                        v___x_4150_ = leanh::lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4199_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_c_4152_ = lean_byte_array_fget(v_array_4143_, v_idx_4144_);
                v___x_4153_ = leanh::lean_unsigned_to_nat(1);
                v___x_4154_ = lean_nat_add(v_idx_4144_, v___x_4153_);
                leanh::lean_dec(v_idx_4144_);
                if v_isShared_4151_ == 0 {
                    leanh::lean_ctor_set(v___x_4150_, 1, v___x_4154_);
                    v_it_x27_4156_ = v___x_4150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4198_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_array_4143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 1, v___x_4154_);
                    v_it_x27_4156_ = v_reuseFailAlloc_4198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4192_ = 28u64;
                v___x_4193_ = lean_uint64_dec_eq(v_shift_4141_, v___x_4192_);
                if v___x_4193_ == 0 {
                    v___y_4189_ = v___x_4193_;
                    state = 5;
                    continue;
                } else {
                    v___x_4194_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4);
                    v___x_4195_ = lean_uint8_land(v_c_4152_, v___x_4194_);
                    v___x_4196_ = 0;
                    v___x_4197_ = lean_uint8_dec_eq(v___x_4195_, v___x_4196_);
                    if v___x_4197_ == 0 {
                        v___y_4189_ = v___x_4193_;
                        state = 5;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_4159_ == 0 {
                    v___x_4160_ = lean_uint64_to_nat(v___y_4158_);
                    v___x_4161_ = lean_nat_to_int(v___x_4160_);
                    v___x_4162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4162_, 0, v_it_x27_4156_);
                    leanh::lean_ctor_set(v___x_4162_, 1, v___x_4161_);
                    return v___x_4162_;
                } else {
                    v___x_4163_ = lean_uint64_to_nat(v___y_4158_);
                    v___x_4164_ = lean_nat_to_int(v___x_4163_);
                    v___x_4165_ = lean_int_neg(v___x_4164_);
                    leanh::lean_dec(v___x_4164_);
                    v___x_4166_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4166_, 0, v_it_x27_4156_);
                    leanh::lean_ctor_set(v___x_4166_, 1, v___x_4165_);
                    return v___x_4166_;
                }
            }
            4 => {
                v___x_4168_ = 0;
                v___x_4169_ = lean_uint8_dec_eq(v_c_4152_, v___x_4168_);
                if v___x_4169_ == 0 {
                    v___x_4170_ = 127;
                    v___x_4171_ = lean_uint8_land(v_c_4152_, v___x_4170_);
                    v___x_4172_ = lean_uint8_to_uint64(v___x_4171_);
                    v___x_4173_ = lean_uint64_shift_left(v___x_4172_, v_shift_4141_);
                    v___x_4174_ = lean_uint64_lor(v_uidx_4140_, v___x_4173_);
                    v___x_4175_ = 128;
                    v___x_4176_ = lean_uint8_land(v_c_4152_, v___x_4175_);
                    v___x_4177_ = lean_uint8_dec_eq(v___x_4176_, v___x_4168_);
                    if v___x_4177_ == 0 {
                        v___x_4178_ = 7u64;
                        v___x_4179_ = lean_uint64_add(v_shift_4141_, v___x_4178_);
                        v_uidx_4140_ = v___x_4174_;
                        v_shift_4141_ = v___x_4179_;
                        v_a_4142_ = v_it_x27_4156_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4181_ = 1u64;
                        v___x_4182_ = lean_uint64_shift_right(v___x_4174_, v___x_4181_);
                        v___x_4183_ = lean_uint64_land(v___x_4181_, v___x_4174_);
                        v___x_4184_ = 0u64;
                        v___x_4185_ = lean_uint64_dec_eq(v___x_4183_, v___x_4184_);
                        if v___x_4185_ == 0 {
                            v___y_4158_ = v___x_4182_;
                            v___y_4159_ = v___x_4177_;
                            state = 3;
                            continue;
                        } else {
                            v___y_4158_ = v___x_4182_;
                            v___y_4159_ = v___x_4169_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_4186_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1;
                    v___x_4187_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4187_, 0, v_it_x27_4156_);
                    leanh::lean_ctor_set(v___x_4187_, 1, v___x_4186_);
                    return v___x_4187_;
                }
            }
            5 => {
                if v___y_4189_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_4190_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3;
                    v___x_4191_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4191_, 0, v_it_x27_4156_);
                    leanh::lean_ctor_set(v___x_4191_, 1, v___x_4190_);
                    return v___x_4191_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(
    mut v_uidx_4202_: *mut leanh::LeanObject,
    mut v_shift_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_uidx_boxed_4205_: u64 = 0;
    let mut v_shift_boxed_4206_: u64 = 0;
    let mut v_res_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_uidx_boxed_4205_ = leanh::lean_unbox_uint64(v_uidx_4202_);
    leanh::lean_dec_ref(v_uidx_4202_);
    v_shift_boxed_4206_ = leanh::lean_unbox_uint64(v_shift_4203_);
    leanh::lean_dec_ref(v_shift_4203_);
    v_res_4207_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_4205_, v_shift_boxed_4206_, v_a_4204_);
    return v_res_4207_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(
    mut v_a_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4209_: u64 = 0;
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = 0u64;
    v___x_4210_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_4209_, v___x_4209_, v_a_4208_);
    return v___x_4210_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(
    mut v_a_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: u8 = 0;
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v_pos_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4215_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4214_);
                if leanh::lean_obj_tag(v___x_4215_) == 0 {
                    v_pos_4216_ = leanh::lean_ctor_get(v___x_4215_, 0);
                    v_res_4217_ = leanh::lean_ctor_get(v___x_4215_, 1);
                    v_isSharedCheck_4231_ = (!leanh::lean_is_exclusive(v___x_4215_)) as u8;
                    if v_isSharedCheck_4231_ == 0 {
                        v___x_4219_ = v___x_4215_;
                        v_isShared_4220_ = v_isSharedCheck_4231_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4217_);
                        leanh::lean_inc(v_pos_4216_);
                        leanh::lean_dec(v___x_4215_);
                        v___x_4219_ = leanh::lean_box(0);
                        v_isShared_4220_ = v_isSharedCheck_4231_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4232_ = leanh::lean_ctor_get(v___x_4215_, 0);
                    v_err_4233_ = leanh::lean_ctor_get(v___x_4215_, 1);
                    v_isSharedCheck_4240_ = (!leanh::lean_is_exclusive(v___x_4215_)) as u8;
                    if v_isSharedCheck_4240_ == 0 {
                        v___x_4235_ = v___x_4215_;
                        v_isShared_4236_ = v_isSharedCheck_4240_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4233_);
                        leanh::lean_inc(v_pos_4232_);
                        leanh::lean_dec(v___x_4215_);
                        v___x_4235_ = leanh::lean_box(0);
                        v_isShared_4236_ = v_isSharedCheck_4240_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4222_ = lean_int_dec_lt(v_res_4217_, v___x_4221_);
                if v___x_4222_ == 0 {
                    leanh::lean_dec(v_res_4217_);
                    v___x_4223_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
                    if v_isShared_4220_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4219_, 1);
                        leanh::lean_ctor_set(v___x_4219_, 1, v___x_4223_);
                        v___x_4225_ = v___x_4219_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4226_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_pos_4216_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 1, v___x_4223_);
                        v___x_4225_ = v_reuseFailAlloc_4226_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4227_ = lean_nat_abs(v_res_4217_);
                    leanh::lean_dec(v_res_4217_);
                    if v_isShared_4220_ == 0 {
                        leanh::lean_ctor_set(v___x_4219_, 1, v___x_4227_);
                        v___x_4229_ = v___x_4219_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_pos_4216_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4227_);
                        v___x_4229_ = v_reuseFailAlloc_4230_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4225_;
            }
            3 => {
                return v___x_4229_;
            }
            4 => {
                if v_isShared_4236_ == 0 {
                    v___x_4238_ = v___x_4235_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4239_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_pos_4232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_err_4233_);
                    v___x_4238_ = v_reuseFailAlloc_4239_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(
    mut v_a_4244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4261_: u8 = 0;
    let mut v_pos_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4244_);
                if leanh::lean_obj_tag(v___x_4245_) == 0 {
                    v_pos_4246_ = leanh::lean_ctor_get(v___x_4245_, 0);
                    v_res_4247_ = leanh::lean_ctor_get(v___x_4245_, 1);
                    v_isSharedCheck_4261_ = (!leanh::lean_is_exclusive(v___x_4245_)) as u8;
                    if v_isSharedCheck_4261_ == 0 {
                        v___x_4249_ = v___x_4245_;
                        v_isShared_4250_ = v_isSharedCheck_4261_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4247_);
                        leanh::lean_inc(v_pos_4246_);
                        leanh::lean_dec(v___x_4245_);
                        v___x_4249_ = leanh::lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4261_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4262_ = leanh::lean_ctor_get(v___x_4245_, 0);
                    v_err_4263_ = leanh::lean_ctor_get(v___x_4245_, 1);
                    v_isSharedCheck_4270_ = (!leanh::lean_is_exclusive(v___x_4245_)) as u8;
                    if v_isSharedCheck_4270_ == 0 {
                        v___x_4265_ = v___x_4245_;
                        v_isShared_4266_ = v_isSharedCheck_4270_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4263_);
                        leanh::lean_inc(v_pos_4262_);
                        leanh::lean_dec(v___x_4245_);
                        v___x_4265_ = leanh::lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4270_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4251_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4252_ = lean_int_dec_lt(v___x_4251_, v_res_4247_);
                if v___x_4252_ == 0 {
                    leanh::lean_dec(v_res_4247_);
                    v___x_4253_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4250_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4249_, 1);
                        leanh::lean_ctor_set(v___x_4249_, 1, v___x_4253_);
                        v___x_4255_ = v___x_4249_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4256_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_pos_4246_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 1, v___x_4253_);
                        v___x_4255_ = v_reuseFailAlloc_4256_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4257_ = lean_nat_abs(v_res_4247_);
                    leanh::lean_dec(v_res_4247_);
                    if v_isShared_4250_ == 0 {
                        leanh::lean_ctor_set(v___x_4249_, 1, v___x_4257_);
                        v___x_4259_ = v___x_4249_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4260_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_pos_4246_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 1, v___x_4257_);
                        v___x_4259_ = v_reuseFailAlloc_4260_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4255_;
            }
            3 => {
                return v___x_4259_;
            }
            4 => {
                if v_isShared_4266_ == 0 {
                    v___x_4268_ = v___x_4265_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_pos_4262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_err_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4269_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(
    mut v_a_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: u8 = 0;
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_pos_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4272_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4271_);
                if leanh::lean_obj_tag(v___x_4272_) == 0 {
                    v_pos_4273_ = leanh::lean_ctor_get(v___x_4272_, 0);
                    v_res_4274_ = leanh::lean_ctor_get(v___x_4272_, 1);
                    v_isSharedCheck_4288_ = (!leanh::lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4288_ == 0 {
                        v___x_4276_ = v___x_4272_;
                        v_isShared_4277_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4274_);
                        leanh::lean_inc(v_pos_4273_);
                        leanh::lean_dec(v___x_4272_);
                        v___x_4276_ = leanh::lean_box(0);
                        v_isShared_4277_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4289_ = leanh::lean_ctor_get(v___x_4272_, 0);
                    v_err_4290_ = leanh::lean_ctor_get(v___x_4272_, 1);
                    v_isSharedCheck_4297_ = (!leanh::lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4297_ == 0 {
                        v___x_4292_ = v___x_4272_;
                        v_isShared_4293_ = v_isSharedCheck_4297_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4290_);
                        leanh::lean_inc(v_pos_4289_);
                        leanh::lean_dec(v___x_4272_);
                        v___x_4292_ = leanh::lean_box(0);
                        v_isShared_4293_ = v_isSharedCheck_4297_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4279_ = lean_int_dec_lt(v___x_4278_, v_res_4274_);
                if v___x_4279_ == 0 {
                    leanh::lean_dec(v_res_4274_);
                    v___x_4280_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4277_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4276_, 1);
                        leanh::lean_ctor_set(v___x_4276_, 1, v___x_4280_);
                        v___x_4282_ = v___x_4276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4283_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_pos_4273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___x_4280_);
                        v___x_4282_ = v_reuseFailAlloc_4283_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4284_ = lean_nat_abs(v_res_4274_);
                    leanh::lean_dec(v_res_4274_);
                    if v_isShared_4277_ == 0 {
                        leanh::lean_ctor_set(v___x_4276_, 1, v___x_4284_);
                        v___x_4286_ = v___x_4276_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_pos_4273_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 1, v___x_4284_);
                        v___x_4286_ = v_reuseFailAlloc_4287_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4282_;
            }
            3 => {
                return v___x_4286_;
            }
            4 => {
                if v_isShared_4293_ == 0 {
                    v___x_4295_ = v___x_4292_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4296_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_pos_4289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_err_4290_);
                    v___x_4295_ = v_reuseFailAlloc_4296_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(
    mut v_parser_4298_: *mut leanh::LeanObject,
    mut v_acc_4299_: *mut leanh::LeanObject,
    mut v_a_4300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: u8 = 0;
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4301_ = leanh::lean_ctor_get(v_a_4300_, 0);
                v_idx_4302_ = leanh::lean_ctor_get(v_a_4300_, 1);
                v___x_4303_ = lean_byte_array_size(v_array_4301_);
                v___x_4304_ = lean_nat_dec_lt(v_idx_4302_, v___x_4303_);
                if v___x_4304_ == 0 {
                    leanh::lean_dec_ref(v_acc_4299_);
                    leanh::lean_dec_ref(v_parser_4298_);
                    v___x_4305_ = leanh::lean_box(0);
                    v___x_4306_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4306_, 0, v_a_4300_);
                    leanh::lean_ctor_set(v___x_4306_, 1, v___x_4305_);
                    return v___x_4306_;
                } else {
                    v___x_4307_ = lean_byte_array_fget(v_array_4301_, v_idx_4302_);
                    v___x_4308_ = 0;
                    v___x_4309_ = lean_uint8_dec_eq(v___x_4307_, v___x_4308_);
                    if v___x_4309_ == 0 {
                        leanh::lean_inc_ref(v_parser_4298_);
                        v___x_4310_ = leanh::lean_apply_1(v_parser_4298_, v_a_4300_);
                        if leanh::lean_obj_tag(v___x_4310_) == 0 {
                            v_pos_4311_ = leanh::lean_ctor_get(v___x_4310_, 0);
                            leanh::lean_inc(v_pos_4311_);
                            v_res_4312_ = leanh::lean_ctor_get(v___x_4310_, 1);
                            leanh::lean_inc(v_res_4312_);
                            leanh::lean_dec_ref_known(v___x_4310_, 2);
                            v___x_4313_ = lean_array_push(v_acc_4299_, v_res_4312_);
                            v_acc_4299_ = v___x_4313_;
                            v_a_4300_ = v_pos_4311_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_acc_4299_);
                            leanh::lean_dec_ref(v_parser_4298_);
                            v_pos_4315_ = leanh::lean_ctor_get(v___x_4310_, 0);
                            v_err_4316_ = leanh::lean_ctor_get(v___x_4310_, 1);
                            v_isSharedCheck_4323_ =
                                (!leanh::lean_is_exclusive(v___x_4310_)) as u8;
                            if v_isSharedCheck_4323_ == 0 {
                                v___x_4318_ = v___x_4310_;
                                v_isShared_4319_ = v_isSharedCheck_4323_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_4316_);
                                leanh::lean_inc(v_pos_4315_);
                                leanh::lean_dec(v___x_4310_);
                                v___x_4318_ = leanh::lean_box(0);
                                v_isShared_4319_ = v_isSharedCheck_4323_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_parser_4298_);
                        v___x_4324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4324_, 0, v_a_4300_);
                        leanh::lean_ctor_set(v___x_4324_, 1, v_acc_4299_);
                        return v___x_4324_;
                    }
                }
            }
            1 => {
                if v_isShared_4319_ == 0 {
                    v___x_4321_ = v___x_4318_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_pos_4315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_err_4316_);
                    v___x_4321_ = v_reuseFailAlloc_4322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(
    mut v_00_u03b1_4325_: *mut leanh::LeanObject,
    mut v_parser_4326_: *mut leanh::LeanObject,
    mut v_acc_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4329_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_4326_, v_acc_4327_, v_a_4328_);
    return v___x_4329_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(
    mut v_parser_4332_: *mut leanh::LeanObject,
    mut v_a_4333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4334_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0;
    v___x_4335_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_4332_, v___x_4334_, v_a_4333_);
    return v___x_4335_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(
    mut v_00_u03b1_4336_: *mut leanh::LeanObject,
    mut v_parser_4337_: *mut leanh::LeanObject,
    mut v_a_4338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_4337_, v_a_4338_);
    return v___x_4339_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(
    mut v_parser_4340_: *mut leanh::LeanObject,
    mut v_acc_4341_: *mut leanh::LeanObject,
    mut v_a_4342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: u8 = 0;
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: u8 = 0;
    let mut v___x_4351_: u8 = 0;
    let mut v___x_4352_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4343_ = leanh::lean_ctor_get(v_a_4342_, 0);
                v_idx_4344_ = leanh::lean_ctor_get(v_a_4342_, 1);
                v___x_4345_ = lean_byte_array_size(v_array_4343_);
                v___x_4346_ = lean_nat_dec_lt(v_idx_4344_, v___x_4345_);
                if v___x_4346_ == 0 {
                    leanh::lean_dec_ref(v_acc_4341_);
                    leanh::lean_dec_ref(v_parser_4340_);
                    v___x_4347_ = leanh::lean_box(0);
                    v___x_4348_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4348_, 0, v_a_4342_);
                    leanh::lean_ctor_set(v___x_4348_, 1, v___x_4347_);
                    return v___x_4348_;
                } else {
                    v___x_4349_ = lean_byte_array_fget(v_array_4343_, v_idx_4344_);
                    v___x_4368_ = 1;
                    v___x_4369_ = lean_uint8_land(v___x_4368_, v___x_4349_);
                    v___x_4370_ = 0;
                    v___x_4371_ = lean_uint8_dec_eq(v___x_4369_, v___x_4370_);
                    if v___x_4371_ == 0 {
                        if v___x_4346_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_parser_4340_);
                            v___x_4372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4372_, 0, v_a_4342_);
                            leanh::lean_ctor_set(v___x_4372_, 1, v_acc_4341_);
                            return v___x_4372_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4351_ = 0;
                v___x_4352_ = lean_uint8_dec_eq(v___x_4349_, v___x_4351_);
                if v___x_4352_ == 0 {
                    leanh::lean_inc_ref(v_parser_4340_);
                    v___x_4353_ = leanh::lean_apply_1(v_parser_4340_, v_a_4342_);
                    if leanh::lean_obj_tag(v___x_4353_) == 0 {
                        v_pos_4354_ = leanh::lean_ctor_get(v___x_4353_, 0);
                        leanh::lean_inc(v_pos_4354_);
                        v_res_4355_ = leanh::lean_ctor_get(v___x_4353_, 1);
                        leanh::lean_inc(v_res_4355_);
                        leanh::lean_dec_ref_known(v___x_4353_, 2);
                        v___x_4356_ = lean_array_push(v_acc_4341_, v_res_4355_);
                        v_acc_4341_ = v___x_4356_;
                        v_a_4342_ = v_pos_4354_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_acc_4341_);
                        leanh::lean_dec_ref(v_parser_4340_);
                        v_pos_4358_ = leanh::lean_ctor_get(v___x_4353_, 0);
                        v_err_4359_ = leanh::lean_ctor_get(v___x_4353_, 1);
                        v_isSharedCheck_4366_ =
                            (!leanh::lean_is_exclusive(v___x_4353_)) as u8;
                        if v_isSharedCheck_4366_ == 0 {
                            v___x_4361_ = v___x_4353_;
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_4359_);
                            leanh::lean_inc(v_pos_4358_);
                            leanh::lean_dec(v___x_4353_);
                            v___x_4361_ = leanh::lean_box(0);
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_parser_4340_);
                    v___x_4367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4367_, 0, v_a_4342_);
                    leanh::lean_ctor_set(v___x_4367_, 1, v_acc_4341_);
                    return v___x_4367_;
                }
            }
            2 => {
                if v_isShared_4362_ == 0 {
                    v___x_4364_ = v___x_4361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_pos_4358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_err_4359_);
                    v___x_4364_ = v_reuseFailAlloc_4365_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(
    mut v_00_u03b1_4373_: *mut leanh::LeanObject,
    mut v_parser_4374_: *mut leanh::LeanObject,
    mut v_acc_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_4374_, v_acc_4375_, v_a_4376_);
    return v___x_4377_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(
    mut v_parser_4378_: *mut leanh::LeanObject,
    mut v_a_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0;
    v___x_4381_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_4378_, v___x_4380_, v_a_4379_);
    return v___x_4381_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(
    mut v_00_u03b1_4382_: *mut leanh::LeanObject,
    mut v_parser_4383_: *mut leanh::LeanObject,
    mut v_a_4384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4385_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(
        v_parser_4383_,
        v_a_4384_,
    );
    return v___x_4385_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(
    mut v_a_4386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4388_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_4387_, v_a_4386_);
    return v___x_4388_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(
    mut v_a_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4391_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_4390_, v_a_4389_);
    return v___x_4391_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(
    mut v_acc_4392_: *mut leanh::LeanObject,
    mut v_a_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: u8 = 0;
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: u8 = 0;
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut v_pos_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: u8 = 0;
    let mut v___x_4432_: u8 = 0;
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4394_ = leanh::lean_ctor_get(v_a_4393_, 0);
                v_idx_4395_ = leanh::lean_ctor_get(v_a_4393_, 1);
                v___x_4396_ = lean_byte_array_size(v_array_4394_);
                v___x_4397_ = lean_nat_dec_lt(v_idx_4395_, v___x_4396_);
                if v___x_4397_ == 0 {
                    leanh::lean_dec_ref(v_acc_4392_);
                    v___x_4398_ = leanh::lean_box(0);
                    v___x_4399_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4399_, 0, v_a_4393_);
                    leanh::lean_ctor_set(v___x_4399_, 1, v___x_4398_);
                    return v___x_4399_;
                } else {
                    v___x_4400_ = lean_byte_array_fget(v_array_4394_, v_idx_4395_);
                    v___x_4430_ = 1;
                    v___x_4431_ = lean_uint8_land(v___x_4430_, v___x_4400_);
                    v___x_4432_ = 0;
                    v___x_4433_ = lean_uint8_dec_eq(v___x_4431_, v___x_4432_);
                    if v___x_4433_ == 0 {
                        if v___x_4397_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_4434_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4434_, 0, v_a_4393_);
                            leanh::lean_ctor_set(v___x_4434_, 1, v_acc_4392_);
                            return v___x_4434_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4402_ = 0;
                v___x_4403_ = lean_uint8_dec_eq(v___x_4400_, v___x_4402_);
                if v___x_4403_ == 0 {
                    v___x_4404_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4393_);
                    if leanh::lean_obj_tag(v___x_4404_) == 0 {
                        v_pos_4405_ = leanh::lean_ctor_get(v___x_4404_, 0);
                        v_res_4406_ = leanh::lean_ctor_get(v___x_4404_, 1);
                        v_isSharedCheck_4419_ =
                            (!leanh::lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4419_ == 0 {
                            v___x_4408_ = v___x_4404_;
                            v_isShared_4409_ = v_isSharedCheck_4419_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_4406_);
                            leanh::lean_inc(v_pos_4405_);
                            leanh::lean_dec(v___x_4404_);
                            v___x_4408_ = leanh::lean_box(0);
                            v_isShared_4409_ = v_isSharedCheck_4419_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_acc_4392_);
                        v_pos_4420_ = leanh::lean_ctor_get(v___x_4404_, 0);
                        v_err_4421_ = leanh::lean_ctor_get(v___x_4404_, 1);
                        v_isSharedCheck_4428_ =
                            (!leanh::lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4428_ == 0 {
                            v___x_4423_ = v___x_4404_;
                            v_isShared_4424_ = v_isSharedCheck_4428_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_4421_);
                            leanh::lean_inc(v_pos_4420_);
                            leanh::lean_dec(v___x_4404_);
                            v___x_4423_ = leanh::lean_box(0);
                            v_isShared_4424_ = v_isSharedCheck_4428_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_4429_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4429_, 0, v_a_4393_);
                    leanh::lean_ctor_set(v___x_4429_, 1, v_acc_4392_);
                    return v___x_4429_;
                }
            }
            2 => {
                v___x_4410_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4411_ = lean_int_dec_lt(v___x_4410_, v_res_4406_);
                if v___x_4411_ == 0 {
                    leanh::lean_dec(v_res_4406_);
                    leanh::lean_dec_ref(v_acc_4392_);
                    v___x_4412_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4409_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4408_, 1);
                        leanh::lean_ctor_set(v___x_4408_, 1, v___x_4412_);
                        v___x_4414_ = v___x_4408_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4415_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_pos_4405_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 1, v___x_4412_);
                        v___x_4414_ = v_reuseFailAlloc_4415_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4408_);
                    v___x_4416_ = lean_nat_abs(v_res_4406_);
                    leanh::lean_dec(v_res_4406_);
                    v___x_4417_ = lean_array_push(v_acc_4392_, v___x_4416_);
                    v_acc_4392_ = v___x_4417_;
                    v_a_4393_ = v_pos_4405_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4414_;
            }
            4 => {
                if v_isShared_4424_ == 0 {
                    v___x_4426_ = v___x_4423_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4427_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_pos_4420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_err_4421_);
                    v___x_4426_ = v_reuseFailAlloc_4427_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(
    mut v_a_4435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4436_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0;
    v___x_4437_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_4436_, v_a_4435_);
    return v___x_4437_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(
    mut v_a_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: u8 = 0;
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut v_pos_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_pos_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4439_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4438_);
                if leanh::lean_obj_tag(v___x_4439_) == 0 {
                    v_pos_4440_ = leanh::lean_ctor_get(v___x_4439_, 0);
                    v_res_4441_ = leanh::lean_ctor_get(v___x_4439_, 1);
                    v_isSharedCheck_4472_ = (!leanh::lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4443_ = v___x_4439_;
                        v_isShared_4444_ = v_isSharedCheck_4472_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4441_);
                        leanh::lean_inc(v_pos_4440_);
                        leanh::lean_dec(v___x_4439_);
                        v___x_4443_ = leanh::lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4472_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4473_ = leanh::lean_ctor_get(v___x_4439_, 0);
                    v_err_4474_ = leanh::lean_ctor_get(v___x_4439_, 1);
                    v_isSharedCheck_4481_ = (!leanh::lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4481_ == 0 {
                        v___x_4476_ = v___x_4439_;
                        v_isShared_4477_ = v_isSharedCheck_4481_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4474_);
                        leanh::lean_inc(v_pos_4473_);
                        leanh::lean_dec(v___x_4439_);
                        v___x_4476_ = leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4481_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4446_ = lean_int_dec_lt(v_res_4441_, v___x_4445_);
                if v___x_4446_ == 0 {
                    leanh::lean_dec(v_res_4441_);
                    v___x_4447_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
                    if v_isShared_4444_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4443_, 1);
                        leanh::lean_ctor_set(v___x_4443_, 1, v___x_4447_);
                        v___x_4449_ = v___x_4443_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4450_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_pos_4440_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 1, v___x_4447_);
                        v___x_4449_ = v_reuseFailAlloc_4450_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4443_);
                    v___x_4451_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_4440_);
                    if leanh::lean_obj_tag(v___x_4451_) == 0 {
                        v_pos_4452_ = leanh::lean_ctor_get(v___x_4451_, 0);
                        v_res_4453_ = leanh::lean_ctor_get(v___x_4451_, 1);
                        v_isSharedCheck_4462_ =
                            (!leanh::lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4462_ == 0 {
                            v___x_4455_ = v___x_4451_;
                            v_isShared_4456_ = v_isSharedCheck_4462_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_4453_);
                            leanh::lean_inc(v_pos_4452_);
                            leanh::lean_dec(v___x_4451_);
                            v___x_4455_ = leanh::lean_box(0);
                            v_isShared_4456_ = v_isSharedCheck_4462_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_4441_);
                        v_pos_4463_ = leanh::lean_ctor_get(v___x_4451_, 0);
                        v_err_4464_ = leanh::lean_ctor_get(v___x_4451_, 1);
                        v_isSharedCheck_4471_ =
                            (!leanh::lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4471_ == 0 {
                            v___x_4466_ = v___x_4451_;
                            v_isShared_4467_ = v_isSharedCheck_4471_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_4464_);
                            leanh::lean_inc(v_pos_4463_);
                            leanh::lean_dec(v___x_4451_);
                            v___x_4466_ = leanh::lean_box(0);
                            v_isShared_4467_ = v_isSharedCheck_4471_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4449_;
            }
            3 => {
                v___x_4457_ = lean_nat_abs(v_res_4441_);
                leanh::lean_dec(v_res_4441_);
                v___x_4458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4458_, 0, v___x_4457_);
                leanh::lean_ctor_set(v___x_4458_, 1, v_res_4453_);
                if v_isShared_4456_ == 0 {
                    leanh::lean_ctor_set(v___x_4455_, 1, v___x_4458_);
                    v___x_4460_ = v___x_4455_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4461_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_pos_4452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 1, v___x_4458_);
                    v___x_4460_ = v_reuseFailAlloc_4461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4460_;
            }
            5 => {
                if v_isShared_4467_ == 0 {
                    v___x_4469_ = v___x_4466_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_pos_4463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_err_4464_);
                    v___x_4469_ = v_reuseFailAlloc_4470_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4469_;
            }
            7 => {
                if v_isShared_4477_ == 0 {
                    v___x_4479_ = v___x_4476_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4480_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_pos_4473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_err_4474_);
                    v___x_4479_ = v_reuseFailAlloc_4480_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(
    mut v_a_4482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4483_ = leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4484_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_4483_, v_a_4482_);
    return v___x_4484_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(
    mut v_acc_4485_: *mut leanh::LeanObject,
    mut v_a_4486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u8 = 0;
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4487_ = leanh::lean_ctor_get(v_a_4486_, 0);
                v_idx_4488_ = leanh::lean_ctor_get(v_a_4486_, 1);
                v___x_4489_ = lean_byte_array_size(v_array_4487_);
                v___x_4490_ = lean_nat_dec_lt(v_idx_4488_, v___x_4489_);
                if v___x_4490_ == 0 {
                    leanh::lean_dec_ref(v_acc_4485_);
                    v___x_4491_ = leanh::lean_box(0);
                    v___x_4492_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4492_, 0, v_a_4486_);
                    leanh::lean_ctor_set(v___x_4492_, 1, v___x_4491_);
                    return v___x_4492_;
                } else {
                    v___x_4493_ = lean_byte_array_fget(v_array_4487_, v_idx_4488_);
                    v___x_4494_ = 0;
                    v___x_4495_ = lean_uint8_dec_eq(v___x_4493_, v___x_4494_);
                    if v___x_4495_ == 0 {
                        v___x_4496_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4486_);
                        if leanh::lean_obj_tag(v___x_4496_) == 0 {
                            v_pos_4497_ = leanh::lean_ctor_get(v___x_4496_, 0);
                            leanh::lean_inc(v_pos_4497_);
                            v_res_4498_ = leanh::lean_ctor_get(v___x_4496_, 1);
                            leanh::lean_inc(v_res_4498_);
                            leanh::lean_dec_ref_known(v___x_4496_, 2);
                            v___x_4499_ = lean_array_push(v_acc_4485_, v_res_4498_);
                            v_acc_4485_ = v___x_4499_;
                            v_a_4486_ = v_pos_4497_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_acc_4485_);
                            v_pos_4501_ = leanh::lean_ctor_get(v___x_4496_, 0);
                            v_err_4502_ = leanh::lean_ctor_get(v___x_4496_, 1);
                            v_isSharedCheck_4509_ =
                                (!leanh::lean_is_exclusive(v___x_4496_)) as u8;
                            if v_isSharedCheck_4509_ == 0 {
                                v___x_4504_ = v___x_4496_;
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_4502_);
                                leanh::lean_inc(v_pos_4501_);
                                leanh::lean_dec(v___x_4496_);
                                v___x_4504_ = leanh::lean_box(0);
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_4510_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4510_, 0, v_a_4486_);
                        leanh::lean_ctor_set(v___x_4510_, 1, v_acc_4485_);
                        return v___x_4510_;
                    }
                }
            }
            1 => {
                if v_isShared_4505_ == 0 {
                    v___x_4507_ = v___x_4504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4508_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_pos_4501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_err_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(
    mut v_a_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0;
    v___x_4513_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_4512_, v_a_4511_);
    return v___x_4513_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(
    mut v_acc_4514_: *mut leanh::LeanObject,
    mut v_a_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4516_ = leanh::lean_ctor_get(v_a_4515_, 0);
                v_idx_4517_ = leanh::lean_ctor_get(v_a_4515_, 1);
                v___x_4518_ = lean_byte_array_size(v_array_4516_);
                v___x_4519_ = lean_nat_dec_lt(v_idx_4517_, v___x_4518_);
                if v___x_4519_ == 0 {
                    leanh::lean_dec_ref(v_acc_4514_);
                    v___x_4520_ = leanh::lean_box(0);
                    v___x_4521_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4521_, 0, v_a_4515_);
                    leanh::lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                    return v___x_4521_;
                } else {
                    v___x_4522_ = lean_byte_array_fget(v_array_4516_, v_idx_4517_);
                    v___x_4523_ = 0;
                    v___x_4524_ = lean_uint8_dec_eq(v___x_4522_, v___x_4523_);
                    if v___x_4524_ == 0 {
                        v___x_4525_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_4515_);
                        if leanh::lean_obj_tag(v___x_4525_) == 0 {
                            v_pos_4526_ = leanh::lean_ctor_get(v___x_4525_, 0);
                            leanh::lean_inc(v_pos_4526_);
                            v_res_4527_ = leanh::lean_ctor_get(v___x_4525_, 1);
                            leanh::lean_inc(v_res_4527_);
                            leanh::lean_dec_ref_known(v___x_4525_, 2);
                            v___x_4528_ = lean_array_push(v_acc_4514_, v_res_4527_);
                            v_acc_4514_ = v___x_4528_;
                            v_a_4515_ = v_pos_4526_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_acc_4514_);
                            v_pos_4530_ = leanh::lean_ctor_get(v___x_4525_, 0);
                            v_err_4531_ = leanh::lean_ctor_get(v___x_4525_, 1);
                            v_isSharedCheck_4538_ =
                                (!leanh::lean_is_exclusive(v___x_4525_)) as u8;
                            if v_isSharedCheck_4538_ == 0 {
                                v___x_4533_ = v___x_4525_;
                                v_isShared_4534_ = v_isSharedCheck_4538_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_err_4531_);
                                leanh::lean_inc(v_pos_4530_);
                                leanh::lean_dec(v___x_4525_);
                                v___x_4533_ = leanh::lean_box(0);
                                v_isShared_4534_ = v_isSharedCheck_4538_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_4539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4539_, 0, v_a_4515_);
                        leanh::lean_ctor_set(v___x_4539_, 1, v_acc_4514_);
                        return v___x_4539_;
                    }
                }
            }
            1 => {
                if v_isShared_4534_ == 0 {
                    v___x_4536_ = v___x_4533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_pos_4530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_err_4531_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(
    mut v_a_4540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4541_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0;
    v___x_4542_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_4541_, v_a_4540_);
    return v___x_4542_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(
    mut v_a_4543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v_array_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: u8 = 0;
    let mut v_got_4572_: u8 = 0;
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v_array_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: u8 = 0;
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_got_4602_: u8 = 0;
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4639_: u8 = 0;
    let mut v_unused_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_pos_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v_pos_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v_reuseFailAlloc_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_unused_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4665_: u8 = 0;
    let mut v_pos_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut v_pos_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4680_: u8 = 0;
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4544_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4543_);
                if leanh::lean_obj_tag(v___x_4544_) == 0 {
                    v_pos_4545_ = leanh::lean_ctor_get(v___x_4544_, 0);
                    v_res_4546_ = leanh::lean_ctor_get(v___x_4544_, 1);
                    v_isSharedCheck_4675_ = (!leanh::lean_is_exclusive(v___x_4544_)) as u8;
                    if v_isSharedCheck_4675_ == 0 {
                        v___x_4548_ = v___x_4544_;
                        v_isShared_4549_ = v_isSharedCheck_4675_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4546_);
                        leanh::lean_inc(v_pos_4545_);
                        leanh::lean_dec(v___x_4544_);
                        v___x_4548_ = leanh::lean_box(0);
                        v_isShared_4549_ = v_isSharedCheck_4675_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4676_ = leanh::lean_ctor_get(v___x_4544_, 0);
                    v_err_4677_ = leanh::lean_ctor_get(v___x_4544_, 1);
                    v_isSharedCheck_4684_ = (!leanh::lean_is_exclusive(v___x_4544_)) as u8;
                    if v_isSharedCheck_4684_ == 0 {
                        v___x_4679_ = v___x_4544_;
                        v_isShared_4680_ = v_isSharedCheck_4684_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4677_);
                        leanh::lean_inc(v_pos_4676_);
                        leanh::lean_dec(v___x_4544_);
                        v___x_4679_ = leanh::lean_box(0);
                        v_isShared_4680_ = v_isSharedCheck_4684_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4550_ = leanh::lean_unsigned_to_nat(0);
                v___x_4551_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4552_ = lean_int_dec_lt(v___x_4551_, v_res_4546_);
                if v___x_4552_ == 0 {
                    leanh::lean_dec(v_res_4546_);
                    v___x_4553_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4549_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4548_, 1);
                        leanh::lean_ctor_set(v___x_4548_, 1, v___x_4553_);
                        v___x_4555_ = v___x_4548_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_pos_4545_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 1, v___x_4553_);
                        v___x_4555_ = v_reuseFailAlloc_4556_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4548_);
                    v___x_4557_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_4545_);
                    if leanh::lean_obj_tag(v___x_4557_) == 0 {
                        v_pos_4558_ = leanh::lean_ctor_get(v___x_4557_, 0);
                        v_res_4559_ = leanh::lean_ctor_get(v___x_4557_, 1);
                        v_isSharedCheck_4665_ =
                            (!leanh::lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4665_ == 0 {
                            v___x_4561_ = v___x_4557_;
                            v_isShared_4562_ = v_isSharedCheck_4665_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_4559_);
                            leanh::lean_inc(v_pos_4558_);
                            leanh::lean_dec(v___x_4557_);
                            v___x_4561_ = leanh::lean_box(0);
                            v_isShared_4562_ = v_isSharedCheck_4665_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_4546_);
                        v_pos_4666_ = leanh::lean_ctor_get(v___x_4557_, 0);
                        v_err_4667_ = leanh::lean_ctor_get(v___x_4557_, 1);
                        v_isSharedCheck_4674_ =
                            (!leanh::lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4674_ == 0 {
                            v___x_4669_ = v___x_4557_;
                            v_isShared_4670_ = v_isSharedCheck_4674_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_4667_);
                            leanh::lean_inc(v_pos_4666_);
                            leanh::lean_dec(v___x_4557_);
                            v___x_4669_ = leanh::lean_box(0);
                            v_isShared_4670_ = v_isSharedCheck_4674_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4555_;
            }
            3 => {
                v_array_4563_ = leanh::lean_ctor_get(v_pos_4558_, 0);
                v_idx_4564_ = leanh::lean_ctor_get(v_pos_4558_, 1);
                v___x_4565_ = lean_byte_array_size(v_array_4563_);
                v___x_4566_ = lean_nat_dec_lt(v_idx_4564_, v___x_4565_);
                if v___x_4566_ == 0 {
                    leanh::lean_dec(v_res_4559_);
                    leanh::lean_dec(v_res_4546_);
                    v___x_4567_ = leanh::lean_box(0);
                    if v_isShared_4562_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4561_, 1);
                        leanh::lean_ctor_set(v___x_4561_, 1, v___x_4567_);
                        v___x_4569_ = v___x_4561_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4570_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_pos_4558_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 1, v___x_4567_);
                        v___x_4569_ = v_reuseFailAlloc_4570_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4571_ = 0;
                    v_got_4572_ = lean_byte_array_fget(v_array_4563_, v_idx_4564_);
                    v___x_4573_ = lean_uint8_dec_eq(v_got_4572_, v___x_4571_);
                    if v___x_4573_ == 0 {
                        leanh::lean_dec(v_res_4559_);
                        leanh::lean_dec(v_res_4546_);
                        v___x_4574_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        if v_isShared_4562_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4561_, 1);
                            leanh::lean_ctor_set(v___x_4561_, 1, v___x_4574_);
                            v___x_4576_ = v___x_4561_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4577_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_pos_4558_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4574_);
                            v___x_4576_ = v_reuseFailAlloc_4577_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_4564_);
                        leanh::lean_inc_ref(v_array_4563_);
                        leanh::lean_del_object(v___x_4561_);
                        v_isSharedCheck_4662_ =
                            (!leanh::lean_is_exclusive(v_pos_4558_)) as u8;
                        if v_isSharedCheck_4662_ == 0 {
                            v_unused_4663_ = leanh::lean_ctor_get(v_pos_4558_, 1);
                            leanh::lean_dec(v_unused_4663_);
                            v_unused_4664_ = leanh::lean_ctor_get(v_pos_4558_, 0);
                            leanh::lean_dec(v_unused_4664_);
                            v___x_4579_ = v_pos_4558_;
                            v_isShared_4580_ = v_isSharedCheck_4662_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_4558_);
                            v___x_4579_ = leanh::lean_box(0);
                            v_isShared_4580_ = v_isSharedCheck_4662_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_4569_;
            }
            5 => {
                return v___x_4576_;
            }
            6 => {
                v___x_4581_ = leanh::lean_unsigned_to_nat(1);
                v___x_4582_ = lean_nat_add(v_idx_4564_, v___x_4581_);
                leanh::lean_dec(v_idx_4564_);
                if v_isShared_4580_ == 0 {
                    leanh::lean_ctor_set(v___x_4579_, 1, v___x_4582_);
                    v___x_4584_ = v___x_4579_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_array_4563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 1, v___x_4582_);
                    v___x_4584_ = v_reuseFailAlloc_4661_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4585_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_4584_);
                if leanh::lean_obj_tag(v___x_4585_) == 0 {
                    v_pos_4586_ = leanh::lean_ctor_get(v___x_4585_, 0);
                    leanh::lean_inc(v_pos_4586_);
                    v_res_4587_ = leanh::lean_ctor_get(v___x_4585_, 1);
                    leanh::lean_inc(v_res_4587_);
                    leanh::lean_dec_ref_known(v___x_4585_, 2);
                    v___x_4588_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_4586_);
                    if leanh::lean_obj_tag(v___x_4588_) == 0 {
                        v_pos_4589_ = leanh::lean_ctor_get(v___x_4588_, 0);
                        v_res_4590_ = leanh::lean_ctor_get(v___x_4588_, 1);
                        v_isSharedCheck_4642_ =
                            (!leanh::lean_is_exclusive(v___x_4588_)) as u8;
                        if v_isSharedCheck_4642_ == 0 {
                            v___x_4592_ = v___x_4588_;
                            v_isShared_4593_ = v_isSharedCheck_4642_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_res_4590_);
                            leanh::lean_inc(v_pos_4589_);
                            leanh::lean_dec(v___x_4588_);
                            v___x_4592_ = leanh::lean_box(0);
                            v_isShared_4593_ = v_isSharedCheck_4642_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_4587_);
                        leanh::lean_dec(v_res_4559_);
                        leanh::lean_dec(v_res_4546_);
                        v_pos_4643_ = leanh::lean_ctor_get(v___x_4588_, 0);
                        v_err_4644_ = leanh::lean_ctor_get(v___x_4588_, 1);
                        v_isSharedCheck_4651_ =
                            (!leanh::lean_is_exclusive(v___x_4588_)) as u8;
                        if v_isSharedCheck_4651_ == 0 {
                            v___x_4646_ = v___x_4588_;
                            v_isShared_4647_ = v_isSharedCheck_4651_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_err_4644_);
                            leanh::lean_inc(v_pos_4643_);
                            leanh::lean_dec(v___x_4588_);
                            v___x_4646_ = leanh::lean_box(0);
                            v_isShared_4647_ = v_isSharedCheck_4651_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_res_4559_);
                    leanh::lean_dec(v_res_4546_);
                    v_pos_4652_ = leanh::lean_ctor_get(v___x_4585_, 0);
                    v_err_4653_ = leanh::lean_ctor_get(v___x_4585_, 1);
                    v_isSharedCheck_4660_ = (!leanh::lean_is_exclusive(v___x_4585_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4655_ = v___x_4585_;
                        v_isShared_4656_ = v_isSharedCheck_4660_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4653_);
                        leanh::lean_inc(v_pos_4652_);
                        leanh::lean_dec(v___x_4585_);
                        v___x_4655_ = leanh::lean_box(0);
                        v_isShared_4656_ = v_isSharedCheck_4660_;
                        state = 19;
                        continue;
                    }
                }
            }
            8 => {
                v_array_4594_ = leanh::lean_ctor_get(v_pos_4589_, 0);
                v_idx_4595_ = leanh::lean_ctor_get(v_pos_4589_, 1);
                v___x_4596_ = lean_byte_array_size(v_array_4594_);
                v___x_4597_ = lean_nat_dec_lt(v_idx_4595_, v___x_4596_);
                if v___x_4597_ == 0 {
                    leanh::lean_dec(v_res_4590_);
                    leanh::lean_dec(v_res_4587_);
                    leanh::lean_dec(v_res_4559_);
                    leanh::lean_dec(v_res_4546_);
                    v___x_4598_ = leanh::lean_box(0);
                    if v_isShared_4593_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4592_, 1);
                        leanh::lean_ctor_set(v___x_4592_, 1, v___x_4598_);
                        v___x_4600_ = v___x_4592_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4601_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_pos_4589_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 1, v___x_4598_);
                        v___x_4600_ = v_reuseFailAlloc_4601_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_got_4602_ = lean_byte_array_fget(v_array_4594_, v_idx_4595_);
                    v___x_4603_ = lean_uint8_dec_eq(v_got_4602_, v___x_4571_);
                    if v___x_4603_ == 0 {
                        leanh::lean_dec(v_res_4590_);
                        leanh::lean_dec(v_res_4587_);
                        leanh::lean_dec(v_res_4559_);
                        leanh::lean_dec(v_res_4546_);
                        v___x_4604_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        if v_isShared_4593_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4592_, 1);
                            leanh::lean_ctor_set(v___x_4592_, 1, v___x_4604_);
                            v___x_4606_ = v___x_4592_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_4607_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_pos_4589_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 1, v___x_4604_);
                            v___x_4606_ = v_reuseFailAlloc_4607_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_4595_);
                        leanh::lean_inc_ref(v_array_4594_);
                        v_isSharedCheck_4639_ =
                            (!leanh::lean_is_exclusive(v_pos_4589_)) as u8;
                        if v_isSharedCheck_4639_ == 0 {
                            v_unused_4640_ = leanh::lean_ctor_get(v_pos_4589_, 1);
                            leanh::lean_dec(v_unused_4640_);
                            v_unused_4641_ = leanh::lean_ctor_get(v_pos_4589_, 0);
                            leanh::lean_dec(v_unused_4641_);
                            v___x_4609_ = v_pos_4589_;
                            v_isShared_4610_ = v_isSharedCheck_4639_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_4589_);
                            v___x_4609_ = leanh::lean_box(0);
                            v_isShared_4610_ = v_isSharedCheck_4639_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_4600_;
            }
            10 => {
                return v___x_4606_;
            }
            11 => {
                v___x_4611_ = lean_nat_abs(v_res_4546_);
                leanh::lean_dec(v_res_4546_);
                v___x_4612_ = lean_nat_add(v_idx_4595_, v___x_4581_);
                leanh::lean_dec(v_idx_4595_);
                if v_isShared_4610_ == 0 {
                    leanh::lean_ctor_set(v___x_4609_, 1, v___x_4612_);
                    v___x_4614_ = v___x_4609_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_array_4594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4612_);
                    v___x_4614_ = v_reuseFailAlloc_4638_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4615_ = lean_array_get_size(v_res_4559_);
                v___x_4616_ = lean_nat_dec_eq(v___x_4615_, v___x_4550_);
                if v___x_4616_ == 0 {
                    v___x_4617_ = lean_array_get_size(v_res_4590_);
                    v___x_4618_ = lean_nat_dec_eq(v___x_4617_, v___x_4550_);
                    if v___x_4618_ == 0 {
                        v___x_4619_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_4559_);
                        v___x_4620_ = leanh::lean_alloc_ctor(2, 5, (0) as u32);
                        leanh::lean_ctor_set(v___x_4620_, 0, v___x_4611_);
                        leanh::lean_ctor_set(v___x_4620_, 1, v_res_4559_);
                        leanh::lean_ctor_set(v___x_4620_, 2, v___x_4619_);
                        leanh::lean_ctor_set(v___x_4620_, 3, v_res_4587_);
                        leanh::lean_ctor_set(v___x_4620_, 4, v_res_4590_);
                        if v_isShared_4593_ == 0 {
                            leanh::lean_ctor_set(v___x_4592_, 1, v___x_4620_);
                            leanh::lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4622_ = v___x_4592_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_4623_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4614_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4623_, 1, v___x_4620_);
                            v___x_4622_ = v_reuseFailAlloc_4623_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_res_4590_);
                        v___x_4624_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_4624_, 0, v___x_4611_);
                        leanh::lean_ctor_set(v___x_4624_, 1, v_res_4559_);
                        leanh::lean_ctor_set(v___x_4624_, 2, v_res_4587_);
                        if v_isShared_4593_ == 0 {
                            leanh::lean_ctor_set(v___x_4592_, 1, v___x_4624_);
                            leanh::lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4626_ = v___x_4592_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4627_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4614_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4627_, 1, v___x_4624_);
                            v___x_4626_ = v_reuseFailAlloc_4627_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_res_4559_);
                    v___x_4628_ = lean_array_get_size(v_res_4590_);
                    leanh::lean_dec(v_res_4590_);
                    v___x_4629_ = lean_nat_dec_eq(v___x_4628_, v___x_4550_);
                    if v___x_4629_ == 0 {
                        leanh::lean_dec(v___x_4611_);
                        leanh::lean_dec(v_res_4587_);
                        v___x_4630_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2;
                        if v_isShared_4593_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4592_, 1);
                            leanh::lean_ctor_set(v___x_4592_, 1, v___x_4630_);
                            leanh::lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4632_ = v___x_4592_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_4633_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4614_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4633_, 1, v___x_4630_);
                            v___x_4632_ = v_reuseFailAlloc_4633_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_4634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4634_, 0, v___x_4611_);
                        leanh::lean_ctor_set(v___x_4634_, 1, v_res_4587_);
                        if v_isShared_4593_ == 0 {
                            leanh::lean_ctor_set(v___x_4592_, 1, v___x_4634_);
                            leanh::lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4636_ = v___x_4592_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_4637_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4614_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 1, v___x_4634_);
                            v___x_4636_ = v_reuseFailAlloc_4637_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            13 => {
                return v___x_4622_;
            }
            14 => {
                return v___x_4626_;
            }
            15 => {
                return v___x_4632_;
            }
            16 => {
                return v___x_4636_;
            }
            17 => {
                if v_isShared_4647_ == 0 {
                    v___x_4649_ = v___x_4646_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_pos_4643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_err_4644_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4649_;
            }
            19 => {
                if v_isShared_4656_ == 0 {
                    v___x_4658_ = v___x_4655_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_pos_4652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_err_4653_);
                    v___x_4658_ = v_reuseFailAlloc_4659_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4658_;
            }
            21 => {
                if v_isShared_4670_ == 0 {
                    v___x_4672_ = v___x_4669_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4673_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_pos_4666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4673_, 1, v_err_4667_);
                    v___x_4672_ = v_reuseFailAlloc_4673_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4672_;
            }
            23 => {
                if v_isShared_4680_ == 0 {
                    v___x_4682_ = v___x_4679_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4683_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_pos_4676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_err_4677_);
                    v___x_4682_ = v_reuseFailAlloc_4683_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(
    mut v_a_4685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v_array_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: u8 = 0;
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut v_got_4701_: u8 = 0;
    let mut v___x_4702_: u8 = 0;
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut v_unused_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4722_: u8 = 0;
    let mut v_pos_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_4685_);
                if leanh::lean_obj_tag(v___x_4686_) == 0 {
                    v_pos_4687_ = leanh::lean_ctor_get(v___x_4686_, 0);
                    v_res_4688_ = leanh::lean_ctor_get(v___x_4686_, 1);
                    v_isSharedCheck_4722_ = (!leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4722_ == 0 {
                        v___x_4690_ = v___x_4686_;
                        v_isShared_4691_ = v_isSharedCheck_4722_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_res_4688_);
                        leanh::lean_inc(v_pos_4687_);
                        leanh::lean_dec(v___x_4686_);
                        v___x_4690_ = leanh::lean_box(0);
                        v_isShared_4691_ = v_isSharedCheck_4722_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4723_ = leanh::lean_ctor_get(v___x_4686_, 0);
                    v_err_4724_ = leanh::lean_ctor_get(v___x_4686_, 1);
                    v_isSharedCheck_4731_ = (!leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4731_ == 0 {
                        v___x_4726_ = v___x_4686_;
                        v_isShared_4727_ = v_isSharedCheck_4731_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4724_);
                        leanh::lean_inc(v_pos_4723_);
                        leanh::lean_dec(v___x_4686_);
                        v___x_4726_ = leanh::lean_box(0);
                        v_isShared_4727_ = v_isSharedCheck_4731_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_array_4692_ = leanh::lean_ctor_get(v_pos_4687_, 0);
                v_idx_4693_ = leanh::lean_ctor_get(v_pos_4687_, 1);
                v___x_4694_ = lean_byte_array_size(v_array_4692_);
                v___x_4695_ = lean_nat_dec_lt(v_idx_4693_, v___x_4694_);
                if v___x_4695_ == 0 {
                    leanh::lean_dec(v_res_4688_);
                    v___x_4696_ = leanh::lean_box(0);
                    if v_isShared_4691_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4690_, 1);
                        leanh::lean_ctor_set(v___x_4690_, 1, v___x_4696_);
                        v___x_4698_ = v___x_4690_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4699_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_pos_4687_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4699_, 1, v___x_4696_);
                        v___x_4698_ = v_reuseFailAlloc_4699_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4700_ = 0;
                    v_got_4701_ = lean_byte_array_fget(v_array_4692_, v_idx_4693_);
                    v___x_4702_ = lean_uint8_dec_eq(v_got_4701_, v___x_4700_);
                    if v___x_4702_ == 0 {
                        leanh::lean_dec(v_res_4688_);
                        v___x_4703_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        if v_isShared_4691_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4690_, 1);
                            leanh::lean_ctor_set(v___x_4690_, 1, v___x_4703_);
                            v___x_4705_ = v___x_4690_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4706_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_pos_4687_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4706_, 1, v___x_4703_);
                            v___x_4705_ = v_reuseFailAlloc_4706_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_idx_4693_);
                        leanh::lean_inc_ref(v_array_4692_);
                        v_isSharedCheck_4719_ =
                            (!leanh::lean_is_exclusive(v_pos_4687_)) as u8;
                        if v_isSharedCheck_4719_ == 0 {
                            v_unused_4720_ = leanh::lean_ctor_get(v_pos_4687_, 1);
                            leanh::lean_dec(v_unused_4720_);
                            v_unused_4721_ = leanh::lean_ctor_get(v_pos_4687_, 0);
                            leanh::lean_dec(v_unused_4721_);
                            v___x_4708_ = v_pos_4687_;
                            v_isShared_4709_ = v_isSharedCheck_4719_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_pos_4687_);
                            v___x_4708_ = leanh::lean_box(0);
                            v_isShared_4709_ = v_isSharedCheck_4719_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4698_;
            }
            3 => {
                return v___x_4705_;
            }
            4 => {
                v___x_4710_ = leanh::lean_unsigned_to_nat(1);
                v___x_4711_ = lean_nat_add(v_idx_4693_, v___x_4710_);
                leanh::lean_dec(v_idx_4693_);
                if v_isShared_4709_ == 0 {
                    leanh::lean_ctor_set(v___x_4708_, 1, v___x_4711_);
                    v___x_4713_ = v___x_4708_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4718_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_array_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4718_, 1, v___x_4711_);
                    v___x_4713_ = v_reuseFailAlloc_4718_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4714_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4714_, 0, v_res_4688_);
                if v_isShared_4691_ == 0 {
                    leanh::lean_ctor_set(v___x_4690_, 1, v___x_4714_);
                    leanh::lean_ctor_set(v___x_4690_, 0, v___x_4713_);
                    v___x_4716_ = v___x_4690_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 1, v___x_4714_);
                    v___x_4716_ = v_reuseFailAlloc_4717_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4716_;
            }
            7 => {
                if v_isShared_4727_ == 0 {
                    v___x_4729_ = v___x_4726_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_pos_4723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_err_4724_);
                    v___x_4729_ = v_reuseFailAlloc_4730_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0() -> u8 {
    let mut v___x_4732_: u32 = 0;
    let mut v___x_4733_: u8 = 0;
    v___x_4732_ = 97;
    v___x_4733_ = lean_uint32_to_uint8(v___x_4732_);
    return v___x_4733_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(
    mut v_a_4735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v_c_4745_: u8 = 0;
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: u8 = 0;
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: u8 = 0;
    let mut v___x_4753_: u8 = 0;
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_unused_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4736_ = leanh::lean_ctor_get(v_a_4735_, 0);
                v_idx_4737_ = leanh::lean_ctor_get(v_a_4735_, 1);
                v___x_4738_ = lean_byte_array_size(v_array_4736_);
                v___x_4739_ = lean_nat_dec_lt(v_idx_4737_, v___x_4738_);
                if v___x_4739_ == 0 {
                    v___x_4740_ = leanh::lean_box(0);
                    v___x_4741_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4741_, 0, v_a_4735_);
                    leanh::lean_ctor_set(v___x_4741_, 1, v___x_4740_);
                    return v___x_4741_;
                } else {
                    leanh::lean_inc(v_idx_4737_);
                    leanh::lean_inc_ref(v_array_4736_);
                    v_isSharedCheck_4763_ = (!leanh::lean_is_exclusive(v_a_4735_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v_unused_4764_ = leanh::lean_ctor_get(v_a_4735_, 1);
                        leanh::lean_dec(v_unused_4764_);
                        v_unused_4765_ = leanh::lean_ctor_get(v_a_4735_, 0);
                        leanh::lean_dec(v_unused_4765_);
                        v___x_4743_ = v_a_4735_;
                        v_isShared_4744_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_4735_);
                        v___x_4743_ = leanh::lean_box(0);
                        v_isShared_4744_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_c_4745_ = lean_byte_array_fget(v_array_4736_, v_idx_4737_);
                v___x_4746_ = leanh::lean_unsigned_to_nat(1);
                v___x_4747_ = lean_nat_add(v_idx_4737_, v___x_4746_);
                leanh::lean_dec(v_idx_4737_);
                if v_isShared_4744_ == 0 {
                    leanh::lean_ctor_set(v___x_4743_, 1, v___x_4747_);
                    v_it_x27_4749_ = v___x_4743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_array_4736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4747_);
                    v_it_x27_4749_ = v_reuseFailAlloc_4762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4750_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once
                    ),
                    _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0,
                );
                v___x_4751_ = lean_uint8_dec_eq(v_c_4745_, v___x_4750_);
                if v___x_4751_ == 0 {
                    v___x_4752_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0,
                    );
                    v___x_4753_ = lean_uint8_dec_eq(v_c_4745_, v___x_4752_);
                    if v___x_4753_ == 0 {
                        v___x_4754_ =
                            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
                        v___x_4755_ = lean_uint8_to_nat(v_c_4745_);
                        v___x_4756_ = l_Nat_reprFast(v___x_4755_);
                        v___x_4757_ = lean_string_append(v___x_4754_, v___x_4756_);
                        leanh::lean_dec_ref(v___x_4756_);
                        v___x_4758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4758_, 0, v___x_4757_);
                        v___x_4759_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4759_, 0, v_it_x27_4749_);
                        leanh::lean_ctor_set(v___x_4759_, 1, v___x_4758_);
                        return v___x_4759_;
                    } else {
                        v___x_4760_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_4749_);
                        return v___x_4760_;
                    }
                } else {
                    v___x_4761_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_4749_);
                    return v___x_4761_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(
    mut v_acc_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v_idx_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: u8 = 0;
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_4767_);
                v___x_4768_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_4767_);
                if leanh::lean_obj_tag(v___x_4768_) == 0 {
                    leanh::lean_dec_ref(v_a_4767_);
                    v_pos_4769_ = leanh::lean_ctor_get(v___x_4768_, 0);
                    leanh::lean_inc(v_pos_4769_);
                    v_res_4770_ = leanh::lean_ctor_get(v___x_4768_, 1);
                    leanh::lean_inc(v_res_4770_);
                    leanh::lean_dec_ref_known(v___x_4768_, 2);
                    v___x_4771_ = lean_array_push(v_acc_4766_, v_res_4770_);
                    v_acc_4766_ = v___x_4771_;
                    v_a_4767_ = v_pos_4769_;
                    state = 0;
                    continue;
                } else {
                    v_pos_4773_ = leanh::lean_ctor_get(v___x_4768_, 0);
                    v_err_4774_ = leanh::lean_ctor_get(v___x_4768_, 1);
                    v_isSharedCheck_4787_ = (!leanh::lean_is_exclusive(v___x_4768_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v___x_4776_ = v___x_4768_;
                        v_isShared_4777_ = v_isSharedCheck_4787_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_err_4774_);
                        leanh::lean_inc(v_pos_4773_);
                        leanh::lean_dec(v___x_4768_);
                        v___x_4776_ = leanh::lean_box(0);
                        v_isShared_4777_ = v_isSharedCheck_4787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_idx_4778_ = leanh::lean_ctor_get(v_a_4767_, 1);
                leanh::lean_inc(v_idx_4778_);
                leanh::lean_dec_ref(v_a_4767_);
                v_idx_4779_ = leanh::lean_ctor_get(v_pos_4773_, 1);
                v___x_4780_ = lean_nat_dec_eq(v_idx_4778_, v_idx_4779_);
                leanh::lean_dec(v_idx_4778_);
                if v___x_4780_ == 0 {
                    leanh::lean_dec_ref(v_acc_4766_);
                    if v_isShared_4777_ == 0 {
                        v___x_4782_ = v___x_4776_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4783_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_pos_4773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 1, v_err_4774_);
                        v___x_4782_ = v_reuseFailAlloc_4783_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_err_4774_);
                    if v_isShared_4777_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4776_, 0);
                        leanh::lean_ctor_set(v___x_4776_, 1, v_acc_4766_);
                        v___x_4785_ = v___x_4776_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_pos_4773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_acc_4766_);
                        v___x_4785_ = v_reuseFailAlloc_4786_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4782_;
            }
            3 => {
                return v___x_4785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(
    mut v_a_4791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: u8 = 0;
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_unused_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4792_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0;
                v___x_4793_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_4792_, v_a_4791_);
                if leanh::lean_obj_tag(v___x_4793_) == 0 {
                    v_pos_4794_ = leanh::lean_ctor_get(v___x_4793_, 0);
                    leanh::lean_inc(v_pos_4794_);
                    v_array_4795_ = leanh::lean_ctor_get(v_pos_4794_, 0);
                    v_idx_4796_ = leanh::lean_ctor_get(v_pos_4794_, 1);
                    v___x_4797_ = lean_byte_array_size(v_array_4795_);
                    v___x_4798_ = lean_nat_dec_lt(v_idx_4796_, v___x_4797_);
                    if v___x_4798_ == 0 {
                        leanh::lean_dec(v_pos_4794_);
                        return v___x_4793_;
                    } else {
                        v_isSharedCheck_4806_ =
                            (!leanh::lean_is_exclusive(v___x_4793_)) as u8;
                        if v_isSharedCheck_4806_ == 0 {
                            v_unused_4807_ = leanh::lean_ctor_get(v___x_4793_, 1);
                            leanh::lean_dec(v_unused_4807_);
                            v_unused_4808_ = leanh::lean_ctor_get(v___x_4793_, 0);
                            leanh::lean_dec(v_unused_4808_);
                            v___x_4800_ = v___x_4793_;
                            v_isShared_4801_ = v_isSharedCheck_4806_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4793_);
                            v___x_4800_ = leanh::lean_box(0);
                            v_isShared_4801_ = v_isSharedCheck_4806_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_4793_;
                }
            }
            1 => {
                v___x_4802_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1;
                if v_isShared_4801_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4800_, 1);
                    leanh::lean_ctor_set(v___x_4800_, 1, v___x_4802_);
                    v___x_4804_ = v___x_4800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4805_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_pos_4794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 1, v___x_4802_);
                    v___x_4804_ = v_reuseFailAlloc_4805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(
    mut v_a_4809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4811_: u8 = 0;
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: u8 = 0;
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v___x_4821_: u8 = 0;
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4814_ = leanh::lean_ctor_get(v_a_4809_, 0);
                v_idx_4815_ = leanh::lean_ctor_get(v_a_4809_, 1);
                v___x_4816_ = lean_byte_array_size(v_array_4814_);
                v___x_4817_ = lean_nat_dec_lt(v_idx_4815_, v___x_4816_);
                if v___x_4817_ == 0 {
                    v___x_4818_ = leanh::lean_box(0);
                    v___x_4819_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4819_, 0, v_a_4809_);
                    leanh::lean_ctor_set(v___x_4819_, 1, v___x_4818_);
                    return v___x_4819_;
                } else {
                    v___x_4820_ = lean_byte_array_fget(v_array_4814_, v_idx_4815_);
                    v___x_4821_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once
                        ),
                        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0,
                    );
                    v___x_4822_ = lean_uint8_dec_eq(v___x_4820_, v___x_4821_);
                    if v___x_4822_ == 0 {
                        v___x_4823_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0,
                        );
                        v___x_4824_ = lean_uint8_dec_eq(v___x_4820_, v___x_4823_);
                        v___y_4811_ = v___x_4824_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4811_ = v___x_4822_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4811_ == 0 {
                    v___x_4812_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_4809_);
                    return v___x_4812_;
                } else {
                    v___x_4813_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_4809_);
                    return v___x_4813_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_loadLRATProof(
    mut v_path_4825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4831_: u8 = 0;
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4844_: u8 = 0;
    let mut v_a_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4827_ = l_IO_FS_readBinFile(v_path_4825_);
                if leanh::lean_obj_tag(v___x_4827_) == 0 {
                    v_a_4828_ = leanh::lean_ctor_get(v___x_4827_, 0);
                    v_isSharedCheck_4849_ = (!leanh::lean_is_exclusive(v___x_4827_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4830_ = v___x_4827_;
                        v_isShared_4831_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4828_);
                        leanh::lean_dec(v___x_4827_);
                        v___x_4830_ = leanh::lean_box(0);
                        v_isShared_4831_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4850_ = leanh::lean_ctor_get(v___x_4827_, 0);
                    v_isSharedCheck_4857_ = (!leanh::lean_is_exclusive(v___x_4827_)) as u8;
                    if v_isSharedCheck_4857_ == 0 {
                        v___x_4852_ = v___x_4827_;
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4850_);
                        leanh::lean_dec(v___x_4827_);
                        v___x_4852_ = leanh::lean_box(0);
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4832_ = leanh::lean_alloc_closure(
                    l_Std_Tactic_BVDecide_LRAT_Parser_parseActions as *mut core::ffi::c_void,
                    1,
                    0,
                );
                v___x_4833_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_4832_, v_a_4828_);
                if leanh::lean_obj_tag(v___x_4833_) == 0 {
                    v_a_4834_ = leanh::lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4844_ = (!leanh::lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4844_ == 0 {
                        v___x_4836_ = v___x_4833_;
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4834_);
                        leanh::lean_dec(v___x_4833_);
                        v___x_4836_ = leanh::lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4845_ = leanh::lean_ctor_get(v___x_4833_, 0);
                    leanh::lean_inc(v_a_4845_);
                    leanh::lean_dec_ref_known(v___x_4833_, 1);
                    if v_isShared_4831_ == 0 {
                        leanh::lean_ctor_set(v___x_4830_, 0, v_a_4845_);
                        v___x_4847_ = v___x_4830_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4845_);
                        v___x_4847_ = v_reuseFailAlloc_4848_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4837_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4836_, 18);
                    v___x_4839_ = v___x_4836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4843_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4834_);
                    v___x_4839_ = v_reuseFailAlloc_4843_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4831_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4830_, 1);
                    leanh::lean_ctor_set(v___x_4830_, 0, v___x_4839_);
                    v___x_4841_ = v___x_4830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4842_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4839_);
                    v___x_4841_ = v_reuseFailAlloc_4842_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4841_;
            }
            5 => {
                return v___x_4847_;
            }
            6 => {
                if v_isShared_4853_ == 0 {
                    v___x_4855_ = v___x_4852_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4856_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
                    v___x_4855_ = v_reuseFailAlloc_4856_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(
    mut v_path_4858_: *mut leanh::LeanObject,
    mut v_a_4859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4860_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_4858_);
    leanh::lean_dec_ref(v_path_4858_);
    return v_res_4860_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_parseLRATProof(
    mut v_proof_4861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4862_ = leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_parseActions as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4863_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_4862_, v_proof_4861_);
    return v___x_4863_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(
    mut v_as_4865_: *mut leanh::LeanObject,
    mut v_i_4866_: usize,
    mut v_stop_4867_: usize,
    mut v_b_4868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: usize = 0;
    let mut v___x_4876_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4869_ = lean_usize_dec_eq(v_i_4866_, v_stop_4867_);
                if v___x_4869_ == 0 {
                    v___x_4870_ = lean_array_uget_borrowed(v_as_4865_, v_i_4866_);
                    leanh::lean_inc(v___x_4870_);
                    v___x_4871_ = l_Nat_reprFast(v___x_4870_);
                    v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
                    v___x_4873_ = lean_string_append(v___x_4871_, v___x_4872_);
                    v___x_4874_ = lean_string_append(v_b_4868_, v___x_4873_);
                    leanh::lean_dec_ref(v___x_4873_);
                    v___x_4875_ = 1usize;
                    v___x_4876_ = lean_usize_add(v_i_4866_, v___x_4875_);
                    v_i_4866_ = v___x_4876_;
                    v_b_4868_ = v___x_4874_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4868_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(
    mut v_as_4878_: *mut leanh::LeanObject,
    mut v_i_4879_: *mut leanh::LeanObject,
    mut v_stop_4880_: *mut leanh::LeanObject,
    mut v_b_4881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4882_: usize = 0;
    let mut v_stop_boxed_4883_: usize = 0;
    let mut v_res_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4882_ = leanh::lean_unbox_usize(v_i_4879_);
    leanh::lean_dec(v_i_4879_);
    v_stop_boxed_4883_ = leanh::lean_unbox_usize(v_stop_4880_);
    leanh::lean_dec(v_stop_4880_);
    v_res_4884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_4878_, v_i_boxed_4882_, v_stop_boxed_4883_, v_b_4881_);
    leanh::lean_dec_ref(v_as_4878_);
    return v_res_4884_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(
    mut v_ids_4886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: u8 = 0;
    v___x_4887_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_4888_ = leanh::lean_unsigned_to_nat(0);
    v___x_4889_ = lean_array_get_size(v_ids_4886_);
    v___x_4890_ = lean_nat_dec_lt(v___x_4888_, v___x_4889_);
    if v___x_4890_ == 0 {
        return v___x_4887_;
    } else {
        let mut v___x_4891_: u8 = 0;
        v___x_4891_ = lean_nat_dec_le(v___x_4889_, v___x_4889_);
        if v___x_4891_ == 0 {
            if v___x_4890_ == 0 {
                return v___x_4887_;
            } else {
                let mut v___x_4892_: usize = 0;
                let mut v___x_4893_: usize = 0;
                let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4892_ = 0usize;
                v___x_4893_ = lean_usize_of_nat(v___x_4889_);
                v___x_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_4886_, v___x_4892_, v___x_4893_, v___x_4887_);
                return v___x_4894_;
            }
        } else {
            let mut v___x_4895_: usize = 0;
            let mut v___x_4896_: usize = 0;
            let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4895_ = 0usize;
            v___x_4896_ = lean_usize_of_nat(v___x_4889_);
            v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_4886_, v___x_4895_, v___x_4896_, v___x_4887_);
            return v___x_4897_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(
    mut v_ids_4898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4899_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_4898_);
    leanh::lean_dec_ref(v_ids_4898_);
    return v_res_4899_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(
    mut v_hint_4901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4902_ = leanh::lean_ctor_get(v_hint_4901_, 0);
    leanh::lean_inc(v_fst_4902_);
    v_snd_4903_ = leanh::lean_ctor_get(v_hint_4901_, 1);
    leanh::lean_inc(v_snd_4903_);
    leanh::lean_dec_ref(v_hint_4901_);
    v___x_4904_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0;
    v___x_4905_ = l_Nat_reprFast(v_fst_4902_);
    v___x_4906_ = lean_string_append(v___x_4904_, v___x_4905_);
    leanh::lean_dec_ref(v___x_4905_);
    v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
    v___x_4908_ = lean_string_append(v___x_4906_, v___x_4907_);
    v___x_4909_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_4903_);
    leanh::lean_dec(v_snd_4903_);
    v___x_4910_ = lean_string_append(v___x_4908_, v___x_4909_);
    leanh::lean_dec_ref(v___x_4909_);
    return v___x_4910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(
    mut v_as_4911_: *mut leanh::LeanObject,
    mut v_i_4912_: usize,
    mut v_stop_4913_: usize,
    mut v_b_4914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4915_: u8 = 0;
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4915_ = lean_usize_dec_eq(v_i_4912_, v_stop_4913_);
                if v___x_4915_ == 0 {
                    v___x_4916_ = lean_array_uget_borrowed(v_as_4911_, v_i_4912_);
                    leanh::lean_inc(v___x_4916_);
                    v___x_4917_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_4916_);
                    v___x_4918_ = lean_string_append(v_b_4914_, v___x_4917_);
                    leanh::lean_dec_ref(v___x_4917_);
                    v___x_4919_ = 1usize;
                    v___x_4920_ = lean_usize_add(v_i_4912_, v___x_4919_);
                    v_i_4912_ = v___x_4920_;
                    v_b_4914_ = v___x_4918_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(
    mut v_as_4922_: *mut leanh::LeanObject,
    mut v_i_4923_: *mut leanh::LeanObject,
    mut v_stop_4924_: *mut leanh::LeanObject,
    mut v_b_4925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4926_: usize = 0;
    let mut v_stop_boxed_4927_: usize = 0;
    let mut v_res_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4926_ = leanh::lean_unbox_usize(v_i_4923_);
    leanh::lean_dec(v_i_4923_);
    v_stop_boxed_4927_ = leanh::lean_unbox_usize(v_stop_4924_);
    leanh::lean_dec(v_stop_4924_);
    v_res_4928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_4922_, v_i_boxed_4926_, v_stop_boxed_4927_, v_b_4925_);
    leanh::lean_dec_ref(v_as_4922_);
    return v_res_4928_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(
    mut v_hints_4929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: u8 = 0;
    v___x_4930_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_4931_ = leanh::lean_unsigned_to_nat(0);
    v___x_4932_ = lean_array_get_size(v_hints_4929_);
    v___x_4933_ = lean_nat_dec_lt(v___x_4931_, v___x_4932_);
    if v___x_4933_ == 0 {
        return v___x_4930_;
    } else {
        let mut v___x_4934_: u8 = 0;
        v___x_4934_ = lean_nat_dec_le(v___x_4932_, v___x_4932_);
        if v___x_4934_ == 0 {
            if v___x_4933_ == 0 {
                return v___x_4930_;
            } else {
                let mut v___x_4935_: usize = 0;
                let mut v___x_4936_: usize = 0;
                let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4935_ = 0usize;
                v___x_4936_ = lean_usize_of_nat(v___x_4932_);
                v___x_4937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_4929_, v___x_4935_, v___x_4936_, v___x_4930_);
                return v___x_4937_;
            }
        } else {
            let mut v___x_4938_: usize = 0;
            let mut v___x_4939_: usize = 0;
            let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4938_ = 0usize;
            v___x_4939_ = lean_usize_of_nat(v___x_4932_);
            v___x_4940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_4929_, v___x_4938_, v___x_4939_, v___x_4930_);
            return v___x_4940_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(
    mut v_hints_4941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4942_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_4941_);
    leanh::lean_dec_ref(v_hints_4941_);
    return v_res_4942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(
    mut v_as_4943_: *mut leanh::LeanObject,
    mut v_i_4944_: usize,
    mut v_stop_4945_: usize,
    mut v_b_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: usize = 0;
    let mut v___x_4954_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4947_ = lean_usize_dec_eq(v_i_4944_, v_stop_4945_);
                if v___x_4947_ == 0 {
                    v___x_4948_ = lean_array_uget_borrowed(v_as_4943_, v_i_4944_);
                    v___x_4949_ = l_Int_repr(v___x_4948_);
                    v___x_4950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
                    v___x_4951_ = lean_string_append(v___x_4949_, v___x_4950_);
                    v___x_4952_ = lean_string_append(v_b_4946_, v___x_4951_);
                    leanh::lean_dec_ref(v___x_4951_);
                    v___x_4953_ = 1usize;
                    v___x_4954_ = lean_usize_add(v_i_4944_, v___x_4953_);
                    v_i_4944_ = v___x_4954_;
                    v_b_4946_ = v___x_4952_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4946_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(
    mut v_as_4956_: *mut leanh::LeanObject,
    mut v_i_4957_: *mut leanh::LeanObject,
    mut v_stop_4958_: *mut leanh::LeanObject,
    mut v_b_4959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4960_: usize = 0;
    let mut v_stop_boxed_4961_: usize = 0;
    let mut v_res_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4960_ = leanh::lean_unbox_usize(v_i_4957_);
    leanh::lean_dec(v_i_4957_);
    v_stop_boxed_4961_ = leanh::lean_unbox_usize(v_stop_4958_);
    leanh::lean_dec(v_stop_4958_);
    v_res_4962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_4956_, v_i_boxed_4960_, v_stop_boxed_4961_, v_b_4959_);
    leanh::lean_dec_ref(v_as_4956_);
    return v_res_4962_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(
    mut v_clause_4963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: u8 = 0;
    v___x_4964_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_4965_ = leanh::lean_unsigned_to_nat(0);
    v___x_4966_ = lean_array_get_size(v_clause_4963_);
    v___x_4967_ = lean_nat_dec_lt(v___x_4965_, v___x_4966_);
    if v___x_4967_ == 0 {
        return v___x_4964_;
    } else {
        let mut v___x_4968_: u8 = 0;
        v___x_4968_ = lean_nat_dec_le(v___x_4966_, v___x_4966_);
        if v___x_4968_ == 0 {
            if v___x_4967_ == 0 {
                return v___x_4964_;
            } else {
                let mut v___x_4969_: usize = 0;
                let mut v___x_4970_: usize = 0;
                let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4969_ = 0usize;
                v___x_4970_ = lean_usize_of_nat(v___x_4966_);
                v___x_4971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_4963_, v___x_4969_, v___x_4970_, v___x_4964_);
                return v___x_4971_;
            }
        } else {
            let mut v___x_4972_: usize = 0;
            let mut v___x_4973_: usize = 0;
            let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4972_ = 0usize;
            v___x_4973_ = lean_usize_of_nat(v___x_4966_);
            v___x_4974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_4963_, v___x_4972_, v___x_4973_, v___x_4964_);
            return v___x_4974_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(
    mut v_clause_4975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4976_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_4975_);
    leanh::lean_dec_ref(v_clause_4975_);
    return v_res_4976_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(
    mut v_a_4981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_a_4981_) {
        0 => {
            let mut v_id_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rupHints_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_id_4982_ = leanh::lean_ctor_get(v_a_4981_, 0);
            leanh::lean_inc(v_id_4982_);
            v_rupHints_4983_ = leanh::lean_ctor_get(v_a_4981_, 1);
            leanh::lean_inc_ref(v_rupHints_4983_);
            leanh::lean_dec_ref_known(v_a_4981_, 2);
            v___x_4984_ = l_Nat_reprFast(v_id_4982_);
            v___x_4985_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0;
            v___x_4986_ = lean_string_append(v___x_4984_, v___x_4985_);
            v___x_4987_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_4983_);
            leanh::lean_dec_ref(v_rupHints_4983_);
            v___x_4988_ = lean_string_append(v___x_4986_, v___x_4987_);
            leanh::lean_dec_ref(v___x_4987_);
            v___x_4989_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_4990_ = lean_string_append(v___x_4988_, v___x_4989_);
            return v___x_4990_;
        }
        1 => {
            let mut v_id_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rupHints_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_id_4991_ = leanh::lean_ctor_get(v_a_4981_, 0);
            leanh::lean_inc(v_id_4991_);
            v_c_4992_ = leanh::lean_ctor_get(v_a_4981_, 1);
            leanh::lean_inc(v_c_4992_);
            v_rupHints_4993_ = leanh::lean_ctor_get(v_a_4981_, 2);
            leanh::lean_inc_ref(v_rupHints_4993_);
            leanh::lean_dec_ref_known(v_a_4981_, 3);
            v___x_4994_ = l_Nat_reprFast(v_id_4991_);
            v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
            v___x_4996_ = lean_string_append(v___x_4994_, v___x_4995_);
            v___x_4997_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_4992_);
            leanh::lean_dec(v_c_4992_);
            v___x_4998_ = lean_string_append(v___x_4996_, v___x_4997_);
            leanh::lean_dec_ref(v___x_4997_);
            v___x_4999_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
            v___x_5000_ = lean_string_append(v___x_4998_, v___x_4999_);
            v___x_5001_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_4993_);
            leanh::lean_dec_ref(v_rupHints_4993_);
            v___x_5002_ = lean_string_append(v___x_5000_, v___x_5001_);
            leanh::lean_dec_ref(v___x_5001_);
            v___x_5003_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_5004_ = lean_string_append(v___x_5002_, v___x_5003_);
            return v___x_5004_;
        }
        2 => {
            let mut v_id_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rupHints_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ratHints_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_id_5005_ = leanh::lean_ctor_get(v_a_4981_, 0);
            leanh::lean_inc(v_id_5005_);
            v_c_5006_ = leanh::lean_ctor_get(v_a_4981_, 1);
            leanh::lean_inc(v_c_5006_);
            v_rupHints_5007_ = leanh::lean_ctor_get(v_a_4981_, 3);
            leanh::lean_inc_ref(v_rupHints_5007_);
            v_ratHints_5008_ = leanh::lean_ctor_get(v_a_4981_, 4);
            leanh::lean_inc_ref(v_ratHints_5008_);
            leanh::lean_dec_ref_known(v_a_4981_, 5);
            v___x_5009_ = l_Nat_reprFast(v_id_5005_);
            v___x_5010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
            v___x_5011_ = lean_string_append(v___x_5009_, v___x_5010_);
            v___x_5012_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_5006_);
            leanh::lean_dec(v_c_5006_);
            v___x_5013_ = lean_string_append(v___x_5011_, v___x_5012_);
            leanh::lean_dec_ref(v___x_5012_);
            v___x_5014_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
            v___x_5015_ = lean_string_append(v___x_5013_, v___x_5014_);
            v___x_5016_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_5007_);
            leanh::lean_dec_ref(v_rupHints_5007_);
            v___x_5017_ = lean_string_append(v___x_5015_, v___x_5016_);
            leanh::lean_dec_ref(v___x_5016_);
            v___x_5018_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_5008_);
            leanh::lean_dec_ref(v_ratHints_5008_);
            v___x_5019_ = lean_string_append(v___x_5017_, v___x_5018_);
            leanh::lean_dec_ref(v___x_5018_);
            v___x_5020_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_5021_ = lean_string_append(v___x_5019_, v___x_5020_);
            return v___x_5021_;
        }
        _ => {
            let mut v_ids_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ids_5022_ = leanh::lean_ctor_get(v_a_4981_, 0);
            leanh::lean_inc_ref(v_ids_5022_);
            leanh::lean_dec_ref_known(v_a_4981_, 1);
            v___x_5023_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3;
            v___x_5024_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_5022_);
            leanh::lean_dec_ref(v_ids_5022_);
            v___x_5025_ = lean_string_append(v___x_5023_, v___x_5024_);
            leanh::lean_dec_ref(v___x_5024_);
            v___x_5026_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_5027_ = lean_string_append(v___x_5025_, v___x_5026_);
            return v___x_5027_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(
    mut v_as_5029_: *mut leanh::LeanObject,
    mut v_i_5030_: usize,
    mut v_stop_5031_: usize,
    mut v_b_5032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5033_: u8 = 0;
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: usize = 0;
    let mut v___x_5040_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5033_ = lean_usize_dec_eq(v_i_5030_, v_stop_5031_);
                if v___x_5033_ == 0 {
                    v___x_5034_ = lean_array_uget_borrowed(v_as_5029_, v_i_5030_);
                    leanh::lean_inc(v___x_5034_);
                    v___x_5035_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_5034_);
                    v___x_5036_ = lean_string_append(v_b_5032_, v___x_5035_);
                    leanh::lean_dec_ref(v___x_5035_);
                    v___x_5037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0;
                    v___x_5038_ = lean_string_append(v___x_5036_, v___x_5037_);
                    v___x_5039_ = 1usize;
                    v___x_5040_ = lean_usize_add(v_i_5030_, v___x_5039_);
                    v_i_5030_ = v___x_5040_;
                    v_b_5032_ = v___x_5038_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(
    mut v_as_5042_: *mut leanh::LeanObject,
    mut v_i_5043_: *mut leanh::LeanObject,
    mut v_stop_5044_: *mut leanh::LeanObject,
    mut v_b_5045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5046_: usize = 0;
    let mut v_stop_boxed_5047_: usize = 0;
    let mut v_res_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5046_ = leanh::lean_unbox_usize(v_i_5043_);
    leanh::lean_dec(v_i_5043_);
    v_stop_boxed_5047_ = leanh::lean_unbox_usize(v_stop_5044_);
    leanh::lean_dec(v_stop_5044_);
    v_res_5048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_5042_, v_i_boxed_5046_, v_stop_boxed_5047_, v_b_5045_);
    leanh::lean_dec_ref(v_as_5042_);
    return v_res_5048_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToString(
    mut v_proof_5049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: u8 = 0;
    v___x_5050_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_5051_ = leanh::lean_unsigned_to_nat(0);
    v___x_5052_ = lean_array_get_size(v_proof_5049_);
    v___x_5053_ = lean_nat_dec_lt(v___x_5051_, v___x_5052_);
    if v___x_5053_ == 0 {
        return v___x_5050_;
    } else {
        let mut v___x_5054_: u8 = 0;
        v___x_5054_ = lean_nat_dec_le(v___x_5052_, v___x_5052_);
        if v___x_5054_ == 0 {
            if v___x_5053_ == 0 {
                return v___x_5050_;
            } else {
                let mut v___x_5055_: usize = 0;
                let mut v___x_5056_: usize = 0;
                let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5055_ = 0usize;
                v___x_5056_ = lean_usize_of_nat(v___x_5052_);
                v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_5049_, v___x_5055_, v___x_5056_, v___x_5050_);
                return v___x_5057_;
            }
        } else {
            let mut v___x_5058_: usize = 0;
            let mut v___x_5059_: usize = 0;
            let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5058_ = 0usize;
            v___x_5059_ = lean_usize_of_nat(v___x_5052_);
            v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_5049_, v___x_5058_, v___x_5059_, v___x_5050_);
            return v___x_5060_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(
    mut v_proof_5061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5062_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_5061_);
    leanh::lean_dec_ref(v_proof_5061_);
    return v_res_5062_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(
    mut v_acc_5063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5064_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0,
    );
    v___x_5065_ = lean_byte_array_push(v_acc_5063_, v___x_5064_);
    return v___x_5065_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(
    mut v_acc_5066_: *mut leanh::LeanObject,
    mut v_lit_5067_: u64,
) -> *mut leanh::LeanObject {
    let mut v___y_5069_: u8 = 0;
    let mut v_acc_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u64 = 0;
    let mut v___x_5072_: u64 = 0;
    let mut v___x_5074_: u64 = 0;
    let mut v___x_5075_: u8 = 0;
    let mut v___x_5076_: u64 = 0;
    let mut v___x_5077_: u8 = 0;
    let mut v___x_5078_: u8 = 0;
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: u8 = 0;
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5082_: u8 = 0;
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: u8 = 0;
    let mut v___x_5085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5074_ = 0u64;
                v___x_5075_ = lean_uint64_dec_eq(v_lit_5067_, v___x_5074_);
                if v___x_5075_ == 0 {
                    v___x_5076_ = 127u64;
                    v___x_5077_ = lean_uint64_dec_lt(v___x_5076_, v_lit_5067_);
                    if v___x_5077_ == 0 {
                        v___x_5078_ = lean_uint64_to_uint8(v_lit_5067_);
                        v___x_5079_ = 127;
                        v___x_5080_ = lean_uint8_land(v___x_5078_, v___x_5079_);
                        v___y_5069_ = v___x_5080_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5081_ = lean_uint64_to_uint8(v_lit_5067_);
                        v___x_5082_ = 127;
                        v___x_5083_ = lean_uint8_land(v___x_5081_, v___x_5082_);
                        v___x_5084_ = 128;
                        v___x_5085_ = lean_uint8_lor(v___x_5083_, v___x_5084_);
                        v___y_5069_ = v___x_5085_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_acc_5066_;
                }
            }
            1 => {
                v_acc_5070_ = lean_byte_array_push(v_acc_5066_, v___y_5069_);
                v___x_5071_ = 7u64;
                v___x_5072_ = lean_uint64_shift_right(v_lit_5067_, v___x_5071_);
                v_acc_5066_ = v_acc_5070_;
                v_lit_5067_ = v___x_5072_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(
    mut v_acc_5086_: *mut leanh::LeanObject,
    mut v_lit_5087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lit_boxed_5088_: u64 = 0;
    let mut v_res_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lit_boxed_5088_ = leanh::lean_unbox_uint64(v_lit_5087_);
    leanh::lean_dec_ref(v_lit_5087_);
    v_res_5089_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_5086_, v_lit_boxed_5088_);
    return v_res_5089_;
}
pub unsafe fn l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(
    mut v_msg_5090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5091_ = l_ByteArray_empty;
    v___x_5092_ = lean_panic_fn_borrowed(v___x_5091_, v_msg_5090_);
    return v___x_5092_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5093_ = leanh::lean_cstr_to_nat(b"18446744073709551615\0".as_ptr().cast());
    return v___x_5093_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5097_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3;
    v___x_5098_ = leanh::lean_unsigned_to_nat(4);
    v___x_5099_ = leanh::lean_unsigned_to_nat(388);
    v___x_5100_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2;
    v___x_5101_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1;
    v___x_5102_ = l_mkPanicMessageWithDecl(
        v___x_5101_,
        v___x_5100_,
        v___x_5099_,
        v___x_5098_,
        v___x_5097_,
    );
    return v___x_5102_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(
    mut v_acc_5103_: *mut leanh::LeanObject,
    mut v_lit_5104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_5111_: u64 = 0;
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5113_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_5114_ = lean_int_dec_lt(v___x_5113_, v_lit_5104_);
                if v___x_5114_ == 0 {
                    v___x_5115_ = leanh::lean_unsigned_to_nat(2);
                    v___x_5116_ = lean_nat_abs(v_lit_5104_);
                    v___x_5117_ = lean_nat_mul(v___x_5115_, v___x_5116_);
                    leanh::lean_dec(v___x_5116_);
                    v___x_5118_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5119_ = lean_nat_add(v___x_5117_, v___x_5118_);
                    leanh::lean_dec(v___x_5117_);
                    v___y_5106_ = v___x_5119_;
                    state = 1;
                    continue;
                } else {
                    v___x_5120_ = leanh::lean_unsigned_to_nat(2);
                    v___x_5121_ = lean_nat_abs(v_lit_5104_);
                    v___x_5122_ = lean_nat_mul(v___x_5120_, v___x_5121_);
                    leanh::lean_dec(v___x_5121_);
                    v___y_5106_ = v___x_5122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5107_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
                v___x_5108_ = lean_nat_dec_le(v___y_5106_, v___x_5107_);
                if v___x_5108_ == 0 {
                    leanh::lean_dec(v___y_5106_);
                    leanh::lean_dec_ref(v_acc_5103_);
                    v___x_5109_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
                    v___x_5110_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_5109_);
                    return v___x_5110_;
                } else {
                    v_mapped_5111_ = lean_uint64_of_nat(v___y_5106_);
                    leanh::lean_dec(v___y_5106_);
                    v___x_5112_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_5103_, v_mapped_5111_);
                    return v___x_5112_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(
    mut v_acc_5123_: *mut leanh::LeanObject,
    mut v_lit_5124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5125_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5123_, v_lit_5124_);
    leanh::lean_dec(v_lit_5124_);
    return v_res_5125_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(
    mut v_acc_5126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5127_ = 0;
    v___x_5128_ = lean_byte_array_push(v_acc_5126_, v___x_5127_);
    return v___x_5128_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(
    mut v_acc_5129_: *mut leanh::LeanObject,
    mut v_n_5130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5131_ = lean_nat_to_int(v_n_5130_);
    v___x_5132_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5129_, v___x_5131_);
    leanh::lean_dec(v___x_5131_);
    return v___x_5132_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(
    mut v_acc_5133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5134_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0,
    );
    v___x_5135_ = lean_byte_array_push(v_acc_5133_, v___x_5134_);
    return v___x_5135_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(
    mut v_as_5136_: *mut leanh::LeanObject,
    mut v_i_5137_: usize,
    mut v_stop_5138_: usize,
    mut v_b_5139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: usize = 0;
    let mut v___x_5145_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5140_ = lean_usize_dec_eq(v_i_5137_, v_stop_5138_);
                if v___x_5140_ == 0 {
                    v___x_5141_ = lean_array_uget_borrowed(v_as_5136_, v_i_5137_);
                    leanh::lean_inc(v___x_5141_);
                    v___x_5142_ = lean_nat_to_int(v___x_5141_);
                    v___x_5143_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5139_, v___x_5142_);
                    leanh::lean_dec(v___x_5142_);
                    v___x_5144_ = 1usize;
                    v___x_5145_ = lean_usize_add(v_i_5137_, v___x_5144_);
                    v_i_5137_ = v___x_5145_;
                    v_b_5139_ = v___x_5143_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(
    mut v_as_5147_: *mut leanh::LeanObject,
    mut v_i_5148_: *mut leanh::LeanObject,
    mut v_stop_5149_: *mut leanh::LeanObject,
    mut v_b_5150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5151_: usize = 0;
    let mut v_stop_boxed_5152_: usize = 0;
    let mut v_res_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5151_ = leanh::lean_unbox_usize(v_i_5148_);
    leanh::lean_dec(v_i_5148_);
    v_stop_boxed_5152_ = leanh::lean_unbox_usize(v_stop_5149_);
    leanh::lean_dec(v_stop_5149_);
    v_res_5153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_5147_, v_i_boxed_5151_, v_stop_boxed_5152_, v_b_5150_);
    leanh::lean_dec_ref(v_as_5147_);
    return v_res_5153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(
    mut v_as_5154_: *mut leanh::LeanObject,
    mut v_i_5155_: usize,
    mut v_stop_5156_: usize,
    mut v_b_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5158_: u8 = 0;
    v___x_5158_ = lean_usize_dec_eq(v_i_5155_, v_stop_5156_);
    if v___x_5158_ == 0 {
        let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: usize = 0;
        let mut v___x_5163_: usize = 0;
        let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5159_ = lean_array_uget_borrowed(v_as_5154_, v_i_5155_);
        leanh::lean_inc(v___x_5159_);
        v___x_5160_ = lean_nat_to_int(v___x_5159_);
        v___x_5161_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5157_, v___x_5160_);
        leanh::lean_dec(v___x_5160_);
        v___x_5162_ = 1usize;
        v___x_5163_ = lean_usize_add(v_i_5155_, v___x_5162_);
        v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_5154_, v___x_5163_, v_stop_5156_, v___x_5161_);
        return v___x_5164_;
    } else {
        return v_b_5157_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(
    mut v_as_5165_: *mut leanh::LeanObject,
    mut v_i_5166_: *mut leanh::LeanObject,
    mut v_stop_5167_: *mut leanh::LeanObject,
    mut v_b_5168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5169_: usize = 0;
    let mut v_stop_boxed_5170_: usize = 0;
    let mut v_res_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5169_ = leanh::lean_unbox_usize(v_i_5166_);
    leanh::lean_dec(v_i_5166_);
    v_stop_boxed_5170_ = leanh::lean_unbox_usize(v_stop_5167_);
    leanh::lean_dec(v_stop_5167_);
    v_res_5171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_5165_, v_i_boxed_5169_, v_stop_boxed_5170_, v_b_5168_);
    leanh::lean_dec_ref(v_as_5165_);
    return v_res_5171_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(
    mut v_as_5172_: *mut leanh::LeanObject,
    mut v_i_5173_: usize,
    mut v_stop_5174_: usize,
    mut v_b_5175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: usize = 0;
    let mut v___x_5179_: usize = 0;
    let mut v___x_5181_: u8 = 0;
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: u8 = 0;
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: usize = 0;
    let mut v___x_5193_: usize = 0;
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: usize = 0;
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5181_ = lean_usize_dec_eq(v_i_5173_, v_stop_5174_);
                if v___x_5181_ == 0 {
                    v___x_5182_ = lean_array_uget_borrowed(v_as_5172_, v_i_5173_);
                    v_fst_5183_ = leanh::lean_ctor_get(v___x_5182_, 0);
                    v_snd_5184_ = leanh::lean_ctor_get(v___x_5182_, 1);
                    v___x_5185_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc(v_fst_5183_);
                    v___x_5186_ = lean_nat_to_int(v_fst_5183_);
                    v___x_5187_ = lean_int_neg(v___x_5186_);
                    leanh::lean_dec(v___x_5186_);
                    v_acc_5188_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5175_, v___x_5187_);
                    leanh::lean_dec(v___x_5187_);
                    v___x_5189_ = lean_array_get_size(v_snd_5184_);
                    v___x_5190_ = lean_nat_dec_lt(v___x_5185_, v___x_5189_);
                    if v___x_5190_ == 0 {
                        v___y_5177_ = v_acc_5188_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5191_ = lean_nat_dec_le(v___x_5189_, v___x_5189_);
                        if v___x_5191_ == 0 {
                            if v___x_5190_ == 0 {
                                v___y_5177_ = v_acc_5188_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5192_ = 0usize;
                                v___x_5193_ = lean_usize_of_nat(v___x_5189_);
                                v___x_5194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_5184_, v___x_5192_, v___x_5193_, v_acc_5188_);
                                v___y_5177_ = v___x_5194_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_5195_ = 0usize;
                            v___x_5196_ = lean_usize_of_nat(v___x_5189_);
                            v___x_5197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_5184_, v___x_5195_, v___x_5196_, v_acc_5188_);
                            v___y_5177_ = v___x_5197_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_5175_;
                }
            }
            1 => {
                v___x_5178_ = 1usize;
                v___x_5179_ = lean_usize_add(v_i_5173_, v___x_5178_);
                v_i_5173_ = v___x_5179_;
                v_b_5175_ = v___y_5177_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(
    mut v_as_5198_: *mut leanh::LeanObject,
    mut v_i_5199_: *mut leanh::LeanObject,
    mut v_stop_5200_: *mut leanh::LeanObject,
    mut v_b_5201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5202_: usize = 0;
    let mut v_stop_boxed_5203_: usize = 0;
    let mut v_res_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5202_ = leanh::lean_unbox_usize(v_i_5199_);
    leanh::lean_dec(v_i_5199_);
    v_stop_boxed_5203_ = leanh::lean_unbox_usize(v_stop_5200_);
    leanh::lean_dec(v_stop_5200_);
    v_res_5204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_5198_, v_i_boxed_5202_, v_stop_boxed_5203_, v_b_5201_);
    leanh::lean_dec_ref(v_as_5198_);
    return v_res_5204_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(
    mut v_as_5205_: *mut leanh::LeanObject,
    mut v_i_5206_: usize,
    mut v_stop_5207_: usize,
    mut v_b_5208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: usize = 0;
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: u8 = 0;
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: usize = 0;
    let mut v___x_5226_: usize = 0;
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: usize = 0;
    let mut v___x_5229_: usize = 0;
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5214_ = lean_usize_dec_eq(v_i_5206_, v_stop_5207_);
                if v___x_5214_ == 0 {
                    v___x_5215_ = lean_array_uget_borrowed(v_as_5205_, v_i_5206_);
                    v_fst_5216_ = leanh::lean_ctor_get(v___x_5215_, 0);
                    v_snd_5217_ = leanh::lean_ctor_get(v___x_5215_, 1);
                    v___x_5218_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc(v_fst_5216_);
                    v___x_5219_ = lean_nat_to_int(v_fst_5216_);
                    v___x_5220_ = lean_int_neg(v___x_5219_);
                    leanh::lean_dec(v___x_5219_);
                    v_acc_5221_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5208_, v___x_5220_);
                    leanh::lean_dec(v___x_5220_);
                    v___x_5222_ = lean_array_get_size(v_snd_5217_);
                    v___x_5223_ = lean_nat_dec_lt(v___x_5218_, v___x_5222_);
                    if v___x_5223_ == 0 {
                        v___y_5210_ = v_acc_5221_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5224_ = lean_nat_dec_le(v___x_5222_, v___x_5222_);
                        if v___x_5224_ == 0 {
                            if v___x_5223_ == 0 {
                                v___y_5210_ = v_acc_5221_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5225_ = 0usize;
                                v___x_5226_ = lean_usize_of_nat(v___x_5222_);
                                v___x_5227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_5217_, v___x_5225_, v___x_5226_, v_acc_5221_);
                                v___y_5210_ = v___x_5227_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_5228_ = 0usize;
                            v___x_5229_ = lean_usize_of_nat(v___x_5222_);
                            v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_5217_, v___x_5228_, v___x_5229_, v_acc_5221_);
                            v___y_5210_ = v___x_5230_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_5208_;
                }
            }
            1 => {
                v___x_5211_ = 1usize;
                v___x_5212_ = lean_usize_add(v_i_5206_, v___x_5211_);
                v___x_5213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_5205_, v___x_5212_, v_stop_5207_, v___y_5210_);
                return v___x_5213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(
    mut v_as_5231_: *mut leanh::LeanObject,
    mut v_i_5232_: *mut leanh::LeanObject,
    mut v_stop_5233_: *mut leanh::LeanObject,
    mut v_b_5234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5235_: usize = 0;
    let mut v_stop_boxed_5236_: usize = 0;
    let mut v_res_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5235_ = leanh::lean_unbox_usize(v_i_5232_);
    leanh::lean_dec(v_i_5232_);
    v_stop_boxed_5236_ = leanh::lean_unbox_usize(v_stop_5233_);
    leanh::lean_dec(v_stop_5233_);
    v_res_5237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_5231_, v_i_boxed_5235_, v_stop_boxed_5236_, v_b_5234_);
    leanh::lean_dec_ref(v_as_5231_);
    return v_res_5237_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(
    mut v_as_5238_: *mut leanh::LeanObject,
    mut v_i_5239_: usize,
    mut v_stop_5240_: usize,
    mut v_b_5241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5242_: u8 = 0;
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: usize = 0;
    let mut v___x_5246_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5242_ = lean_usize_dec_eq(v_i_5239_, v_stop_5240_);
                if v___x_5242_ == 0 {
                    v___x_5243_ = lean_array_uget_borrowed(v_as_5238_, v_i_5239_);
                    v___x_5244_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5241_, v___x_5243_);
                    v___x_5245_ = 1usize;
                    v___x_5246_ = lean_usize_add(v_i_5239_, v___x_5245_);
                    v_i_5239_ = v___x_5246_;
                    v_b_5241_ = v___x_5244_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5241_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(
    mut v_as_5248_: *mut leanh::LeanObject,
    mut v_i_5249_: *mut leanh::LeanObject,
    mut v_stop_5250_: *mut leanh::LeanObject,
    mut v_b_5251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5252_: usize = 0;
    let mut v_stop_boxed_5253_: usize = 0;
    let mut v_res_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5252_ = leanh::lean_unbox_usize(v_i_5249_);
    leanh::lean_dec(v_i_5249_);
    v_stop_boxed_5253_ = leanh::lean_unbox_usize(v_stop_5250_);
    leanh::lean_dec(v_stop_5250_);
    v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_5248_, v_i_boxed_5252_, v_stop_boxed_5253_, v_b_5251_);
    leanh::lean_dec_ref(v_as_5248_);
    return v_res_5254_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(
    mut v_proof_5255_: *mut leanh::LeanObject,
    mut v_idx_5256_: *mut leanh::LeanObject,
    mut v_acc_5257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    let mut v_acc_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v_acc_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: u8 = 0;
    let mut v_acc_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: u8 = 0;
    let mut v_acc_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: u8 = 0;
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    let mut v_acc_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: u8 = 0;
    let mut v_acc_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: u8 = 0;
    let mut v___x_5293_: u8 = 0;
    let mut v___x_5294_: usize = 0;
    let mut v___x_5295_: usize = 0;
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: usize = 0;
    let mut v___x_5298_: usize = 0;
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: u8 = 0;
    let mut v_acc_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: u8 = 0;
    let mut v_acc_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: u8 = 0;
    let mut v___x_5314_: u8 = 0;
    let mut v___x_5315_: usize = 0;
    let mut v___x_5316_: usize = 0;
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: usize = 0;
    let mut v___x_5319_: usize = 0;
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: u8 = 0;
    let mut v___x_5324_: usize = 0;
    let mut v___x_5325_: usize = 0;
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: usize = 0;
    let mut v___x_5328_: usize = 0;
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: u8 = 0;
    let mut v_acc_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: u8 = 0;
    let mut v___x_5343_: u8 = 0;
    let mut v___x_5344_: usize = 0;
    let mut v___x_5345_: usize = 0;
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v_acc_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: usize = 0;
    let mut v___x_5358_: usize = 0;
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: u8 = 0;
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5366_: usize = 0;
    let mut v___x_5367_: usize = 0;
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: usize = 0;
    let mut v___x_5370_: usize = 0;
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: u8 = 0;
    let mut v_acc_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: u8 = 0;
    let mut v___x_5379_: usize = 0;
    let mut v___x_5380_: usize = 0;
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: usize = 0;
    let mut v___x_5383_: usize = 0;
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5279_ = lean_array_get_size(v_proof_5255_);
                v___x_5280_ = lean_nat_dec_lt(v_idx_5256_, v___x_5279_);
                if v___x_5280_ == 0 {
                    leanh::lean_dec(v_idx_5256_);
                    return v_acc_5257_;
                } else {
                    v___x_5281_ = lean_array_fget_borrowed(v_proof_5255_, v_idx_5256_);
                    match leanh::lean_obj_tag(v___x_5281_) {
                        0 => {
                            v_id_5282_ = leanh::lean_ctor_get(v___x_5281_, 0);
                            v_rupHints_5283_ = leanh::lean_ctor_get(v___x_5281_, 1);
                            v___x_5284_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
                            v_acc_5285_ = lean_byte_array_push(v_acc_5257_, v___x_5284_);
                            leanh::lean_inc(v_id_5282_);
                            v___x_5286_ = lean_nat_to_int(v_id_5282_);
                            v_acc_5287_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5285_, v___x_5286_);
                            leanh::lean_dec(v___x_5286_);
                            v___x_5288_ = 0;
                            v_acc_5289_ = lean_byte_array_push(v_acc_5287_, v___x_5288_);
                            v___x_5290_ = leanh::lean_unsigned_to_nat(0);
                            v___x_5291_ = lean_array_get_size(v_rupHints_5283_);
                            v___x_5292_ = lean_nat_dec_lt(v___x_5290_, v___x_5291_);
                            if v___x_5292_ == 0 {
                                v___y_5268_ = v_acc_5289_;
                                state = 3;
                                continue;
                            } else {
                                v___x_5293_ = lean_nat_dec_le(v___x_5291_, v___x_5291_);
                                if v___x_5293_ == 0 {
                                    if v___x_5292_ == 0 {
                                        v___y_5268_ = v_acc_5289_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_5294_ = 0usize;
                                        v___x_5295_ = lean_usize_of_nat(v___x_5291_);
                                        v___x_5296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_5283_, v___x_5294_, v___x_5295_, v_acc_5289_);
                                        v___y_5268_ = v___x_5296_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    v___x_5297_ = 0usize;
                                    v___x_5298_ = lean_usize_of_nat(v___x_5291_);
                                    v___x_5299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_5283_, v___x_5297_, v___x_5298_, v_acc_5289_);
                                    v___y_5268_ = v___x_5299_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_id_5300_ = leanh::lean_ctor_get(v___x_5281_, 0);
                            v_c_5301_ = leanh::lean_ctor_get(v___x_5281_, 1);
                            v_rupHints_5302_ = leanh::lean_ctor_get(v___x_5281_, 2);
                            v___x_5303_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
                            v_acc_5304_ = lean_byte_array_push(v_acc_5257_, v___x_5303_);
                            leanh::lean_inc(v_id_5300_);
                            v___x_5305_ = lean_nat_to_int(v_id_5300_);
                            v_acc_5306_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5304_, v___x_5305_);
                            leanh::lean_dec(v___x_5305_);
                            v___x_5307_ = leanh::lean_unsigned_to_nat(0);
                            v___x_5321_ = lean_array_get_size(v_c_5301_);
                            v___x_5322_ = lean_nat_dec_lt(v___x_5307_, v___x_5321_);
                            if v___x_5322_ == 0 {
                                v___y_5309_ = v_acc_5306_;
                                state = 6;
                                continue;
                            } else {
                                v___x_5323_ = lean_nat_dec_le(v___x_5321_, v___x_5321_);
                                if v___x_5323_ == 0 {
                                    if v___x_5322_ == 0 {
                                        v___y_5309_ = v_acc_5306_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___x_5324_ = 0usize;
                                        v___x_5325_ = lean_usize_of_nat(v___x_5321_);
                                        v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_5301_, v___x_5324_, v___x_5325_, v_acc_5306_);
                                        v___y_5309_ = v___x_5326_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    v___x_5327_ = 0usize;
                                    v___x_5328_ = lean_usize_of_nat(v___x_5321_);
                                    v___x_5329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_5301_, v___x_5327_, v___x_5328_, v_acc_5306_);
                                    v___y_5309_ = v___x_5329_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                        2 => {
                            v_id_5330_ = leanh::lean_ctor_get(v___x_5281_, 0);
                            v_c_5331_ = leanh::lean_ctor_get(v___x_5281_, 1);
                            v_rupHints_5332_ = leanh::lean_ctor_get(v___x_5281_, 3);
                            v_ratHints_5333_ = leanh::lean_ctor_get(v___x_5281_, 4);
                            v___x_5334_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
                            v_acc_5335_ = lean_byte_array_push(v_acc_5257_, v___x_5334_);
                            leanh::lean_inc(v_id_5330_);
                            v___x_5336_ = lean_nat_to_int(v_id_5330_);
                            v_acc_5337_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5335_, v___x_5336_);
                            leanh::lean_dec(v___x_5336_);
                            v___x_5338_ = leanh::lean_unsigned_to_nat(0);
                            v___x_5363_ = lean_array_get_size(v_c_5331_);
                            v___x_5364_ = lean_nat_dec_lt(v___x_5338_, v___x_5363_);
                            if v___x_5364_ == 0 {
                                v___y_5351_ = v_acc_5337_;
                                state = 8;
                                continue;
                            } else {
                                v___x_5365_ = lean_nat_dec_le(v___x_5363_, v___x_5363_);
                                if v___x_5365_ == 0 {
                                    if v___x_5364_ == 0 {
                                        v___y_5351_ = v_acc_5337_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_5366_ = 0usize;
                                        v___x_5367_ = lean_usize_of_nat(v___x_5363_);
                                        v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_5331_, v___x_5366_, v___x_5367_, v_acc_5337_);
                                        v___y_5351_ = v___x_5368_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v___x_5369_ = 0usize;
                                    v___x_5370_ = lean_usize_of_nat(v___x_5363_);
                                    v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_5331_, v___x_5369_, v___x_5370_, v_acc_5337_);
                                    v___y_5351_ = v___x_5371_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_ids_5372_ = leanh::lean_ctor_get(v___x_5281_, 0);
                            v___x_5373_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
                            v_acc_5374_ = lean_byte_array_push(v_acc_5257_, v___x_5373_);
                            v___x_5375_ = leanh::lean_unsigned_to_nat(0);
                            v___x_5376_ = lean_array_get_size(v_ids_5372_);
                            v___x_5377_ = lean_nat_dec_lt(v___x_5375_, v___x_5376_);
                            if v___x_5377_ == 0 {
                                v___y_5276_ = v_acc_5374_;
                                state = 5;
                                continue;
                            } else {
                                v___x_5378_ = lean_nat_dec_le(v___x_5376_, v___x_5376_);
                                if v___x_5378_ == 0 {
                                    if v___x_5377_ == 0 {
                                        v___y_5276_ = v_acc_5374_;
                                        state = 5;
                                        continue;
                                    } else {
                                        v___x_5379_ = 0usize;
                                        v___x_5380_ = lean_usize_of_nat(v___x_5376_);
                                        v___x_5381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_5372_, v___x_5379_, v___x_5380_, v_acc_5374_);
                                        v___y_5276_ = v___x_5381_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    v___x_5382_ = 0usize;
                                    v___x_5383_ = lean_usize_of_nat(v___x_5376_);
                                    v___x_5384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_5372_, v___x_5382_, v___x_5383_, v_acc_5374_);
                                    v___y_5276_ = v___x_5384_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5260_ = leanh::lean_unsigned_to_nat(1);
                v___x_5261_ = lean_nat_add(v_idx_5256_, v___x_5260_);
                leanh::lean_dec(v_idx_5256_);
                v_idx_5256_ = v___x_5261_;
                v_acc_5257_ = v___y_5259_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5265_ = 0;
                v_acc_5266_ = lean_byte_array_push(v___y_5264_, v___x_5265_);
                v___y_5259_ = v_acc_5266_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5269_ = 0;
                v_acc_5270_ = lean_byte_array_push(v___y_5268_, v___x_5269_);
                v___y_5259_ = v_acc_5270_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5273_ = 0;
                v_acc_5274_ = lean_byte_array_push(v___y_5272_, v___x_5273_);
                v___y_5259_ = v_acc_5274_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5277_ = 0;
                v_acc_5278_ = lean_byte_array_push(v___y_5276_, v___x_5277_);
                v___y_5259_ = v_acc_5278_;
                state = 1;
                continue;
            }
            6 => {
                v___x_5310_ = 0;
                v_acc_5311_ = lean_byte_array_push(v___y_5309_, v___x_5310_);
                v___x_5312_ = lean_array_get_size(v_rupHints_5302_);
                v___x_5313_ = lean_nat_dec_lt(v___x_5307_, v___x_5312_);
                if v___x_5313_ == 0 {
                    v___y_5272_ = v_acc_5311_;
                    state = 4;
                    continue;
                } else {
                    v___x_5314_ = lean_nat_dec_le(v___x_5312_, v___x_5312_);
                    if v___x_5314_ == 0 {
                        if v___x_5313_ == 0 {
                            v___y_5272_ = v_acc_5311_;
                            state = 4;
                            continue;
                        } else {
                            v___x_5315_ = 0usize;
                            v___x_5316_ = lean_usize_of_nat(v___x_5312_);
                            v___x_5317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_5302_, v___x_5315_, v___x_5316_, v_acc_5311_);
                            v___y_5272_ = v___x_5317_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_5318_ = 0usize;
                        v___x_5319_ = lean_usize_of_nat(v___x_5312_);
                        v___x_5320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_5302_, v___x_5318_, v___x_5319_, v_acc_5311_);
                        v___y_5272_ = v___x_5320_;
                        state = 4;
                        continue;
                    }
                }
            }
            7 => {
                v___x_5341_ = lean_array_get_size(v_ratHints_5333_);
                v___x_5342_ = lean_nat_dec_lt(v___x_5338_, v___x_5341_);
                if v___x_5342_ == 0 {
                    v___y_5264_ = v___y_5340_;
                    state = 2;
                    continue;
                } else {
                    v___x_5343_ = lean_nat_dec_le(v___x_5341_, v___x_5341_);
                    if v___x_5343_ == 0 {
                        if v___x_5342_ == 0 {
                            v___y_5264_ = v___y_5340_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5344_ = 0usize;
                            v___x_5345_ = lean_usize_of_nat(v___x_5341_);
                            v___x_5346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_5333_, v___x_5344_, v___x_5345_, v___y_5340_);
                            v___y_5264_ = v___x_5346_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_5347_ = 0usize;
                        v___x_5348_ = lean_usize_of_nat(v___x_5341_);
                        v___x_5349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_5333_, v___x_5347_, v___x_5348_, v___y_5340_);
                        v___y_5264_ = v___x_5349_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                v___x_5352_ = 0;
                v_acc_5353_ = lean_byte_array_push(v___y_5351_, v___x_5352_);
                v___x_5354_ = lean_array_get_size(v_rupHints_5332_);
                v___x_5355_ = lean_nat_dec_lt(v___x_5338_, v___x_5354_);
                if v___x_5355_ == 0 {
                    v___y_5340_ = v_acc_5353_;
                    state = 7;
                    continue;
                } else {
                    v___x_5356_ = lean_nat_dec_le(v___x_5354_, v___x_5354_);
                    if v___x_5356_ == 0 {
                        if v___x_5355_ == 0 {
                            v___y_5340_ = v_acc_5353_;
                            state = 7;
                            continue;
                        } else {
                            v___x_5357_ = 0usize;
                            v___x_5358_ = lean_usize_of_nat(v___x_5354_);
                            v___x_5359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_5332_, v___x_5357_, v___x_5358_, v_acc_5353_);
                            v___y_5340_ = v___x_5359_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_5360_ = 0usize;
                        v___x_5361_ = lean_usize_of_nat(v___x_5354_);
                        v___x_5362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_5332_, v___x_5360_, v___x_5361_, v_acc_5353_);
                        v___y_5340_ = v___x_5362_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(
    mut v_proof_5385_: *mut leanh::LeanObject,
    mut v_idx_5386_: *mut leanh::LeanObject,
    mut v_acc_5387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5388_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_5385_, v_idx_5386_, v_acc_5387_);
    leanh::lean_dec_ref(v_proof_5385_);
    return v_res_5388_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(
    mut v_proof_5389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5390_ = leanh::lean_unsigned_to_nat(0);
    v___x_5391_ = leanh::lean_unsigned_to_nat(4);
    v___x_5392_ = lean_array_get_size(v_proof_5389_);
    v___x_5393_ = lean_nat_mul(v___x_5391_, v___x_5392_);
    v___x_5394_ = lean_mk_empty_byte_array(v___x_5393_);
    leanh::lean_dec(v___x_5393_);
    v___x_5395_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_5389_, v___x_5390_, v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(
    mut v_proof_5396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5397_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_5396_);
    leanh::lean_dec_ref(v_proof_5396_);
    return v_res_5397_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(
    mut v_path_5398_: *mut leanh::LeanObject,
    mut v_proof_5399_: *mut leanh::LeanObject,
    mut v_binaryProofs_5400_: u8,
) -> *mut leanh::LeanObject {
    if v_binaryProofs_5400_ == 0 {
        let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5402_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_5399_);
        v___x_5403_ = lean_string_to_utf8(v___x_5402_);
        leanh::lean_dec_ref(v___x_5402_);
        v___x_5404_ = l_IO_FS_writeBinFile(v_path_5398_, v___x_5403_);
        leanh::lean_dec_ref(v___x_5403_);
        return v___x_5404_;
    } else {
        let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5405_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_5399_);
        v___x_5406_ = l_IO_FS_writeBinFile(v_path_5398_, v___x_5405_);
        leanh::lean_dec_ref(v___x_5405_);
        return v___x_5406_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(
    mut v_path_5407_: *mut leanh::LeanObject,
    mut v_proof_5408_: *mut leanh::LeanObject,
    mut v_binaryProofs_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binaryProofs_boxed_5411_: u8 = 0;
    let mut v_res_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binaryProofs_boxed_5411_ = (leanh::lean_unbox(v_binaryProofs_5409_) as u8);
    v_res_5412_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(
        v_path_5407_,
        v_proof_5408_,
        v_binaryProofs_boxed_5411_,
    );
    leanh::lean_dec_ref(v_proof_5408_);
    leanh::lean_dec_ref(v_path_5407_);
    return v_res_5412_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Parser(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
}