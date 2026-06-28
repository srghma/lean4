// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Parser
// Imports: Init.System.IO Std.Tactic.BVDecide.LRAT.Actions Std.Internal.Parsec
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_fget;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint8_complement, lean_uint8_land, lean_uint8_lor, lean_uint8_sub, lean_uint64_add,
    lean_uint64_dec_lt, lean_uint64_land, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint8_to_uint32, lean_uint8_to_uint64, lean_uint32_to_uint8,
    lean_uint64_of_nat, lean_uint64_to_nat, lean_uint64_to_uint8, lean_usize_add,
    lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_byte_array_push, lean_byte_array_size, lean_mk_empty_array_with_capacity,
    lean_mk_empty_byte_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_panic_fn_borrowed, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint64_dec_eq,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_cstr_to_nat, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint8_once,
    lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2: u8 = 0;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0: u8 = 0;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0: u8 = 0;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0: u8 = 0;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value: LeanStringObject<57> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 57,
        m_capacity: 57,
        m_length: 56,
        m_data: [
            84, 104, 101, 114, 101, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 97, 110, 121,
            32, 114, 97, 116, 72, 105, 110, 116, 115, 32, 102, 111, 114, 32, 97, 100, 100, 105,
            110, 103, 32, 116, 104, 101, 32, 101, 109, 112, 116, 121, 32, 99, 108, 97, 117, 115,
            101, 0,
        ],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 97, 116, 105, 115, 102, 105, 101, 100, 0]};
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2: u8 = 0;
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3: u8 = 0;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 122, 101, 114, 111, 32, 98, 121, 116, 101, 32, 105, 110, 32, 108, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [69, 120, 99, 101, 115, 115, 105, 118, 101, 32, 108, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value) as *mut LeanObject] };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value) as *mut LeanObject;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value: LeanStringObject<
    52,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value: LeanStringObject<
    52,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0_value
) as *mut LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 48, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [48, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [49, 32, 100, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value: LeanStringObject<93> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 80, 97, 114, 115, 101, 114, 46, 48, 46, 83, 116, 100, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 108, 114, 97, 116, 80, 114, 111, 111, 102, 84, 111, 66, 105, 110, 97, 114, 121, 46, 97, 100, 100, 73, 110, 116, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value: LeanStringObject<94> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 91, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 109, 97, 112, 112, 101, 100, 32, 226, 137, 164, 32, 40, 50, 94, 54, 52, 32, 45, 32, 49, 41, 32, 45, 45, 32, 111, 117, 114, 32, 112, 97, 114, 115, 101, 114, 32, 34, 111, 110, 108, 121, 34, 32, 115, 117, 112, 112, 111, 114, 116, 115, 32, 54, 52, 32, 98, 105, 116, 32, 108, 105, 116, 101, 114, 97, 108, 115, 10, 32, 32, 32, 32, 0]};
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value) as *mut LeanObject;
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0()
-> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    v___x_2707_ = lean_unsigned_to_nat(0);
    v___x_2708_ = lean_nat_to_int(v___x_2707_);
    return v___x_2708_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(
    mut v_clause_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivotInt_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2710_ = l_Int_instInhabited;
    v___x_2711_ = lean_unsigned_to_nat(0);
    v_pivotInt_2712_ = lean_array_get_borrowed(v___x_2710_, v_clause_2709_, v___x_2711_);
    v___x_2713_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
    v___x_2714_ = lean_int_dec_lt(v___x_2713_, v_pivotInt_2712_);
    v___x_2715_ = lean_nat_abs(v_pivotInt_2712_);
    v___x_2716_ = lean_box((v___x_2714_) as usize);
    v___x_2717_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2717_, 0, v___x_2715_);
    lean_ctor_set(v___x_2717_, 1, v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(
    mut v_clause_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_res_2719_ =
        l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(
            v_clause_2718_,
        );
    lean_dec_ref(v_clause_2718_);
    return v_res_2719_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1()
-> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_2722_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    v___x_2726_ = lean_uint8_once(
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
-> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    v___x_2728_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    v___x_2734_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_2735_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    v___x_2737_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8,
    );
    v___x_2738_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2738_, 0, v___x_2737_);
    return v___x_2738_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(
    mut v_a_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v_utf8_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v_unused_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v_got_2764_: u8 = 0;
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2770_: u8 = 0;
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_unused_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2740_ = lean_ctor_get(v_a_2739_, 0);
                v_idx_2741_ = lean_ctor_get(v_a_2739_, 1);
                lean_inc(v_idx_2741_);
                v___x_2759_ = lean_byte_array_size(v_array_2740_);
                v___x_2760_ = lean_nat_dec_lt(v_idx_2741_, v___x_2759_);
                if v___x_2760_ == 0 {
                    v___x_2761_ = lean_box(0);
                    lean_inc_ref(v_a_2739_);
                    v___x_2762_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2762_, 0, v_a_2739_);
                    lean_ctor_set(v___x_2762_, 1, v___x_2761_);
                    lean_inc(v_idx_2741_);
                    v___y_2743_ = v___x_2762_;
                    v_pos_2744_ = v_a_2739_;
                    v_idx_2745_ = v_idx_2741_;
                    state = 1;
                    continue;
                } else {
                    v___x_2763_ = lean_uint8_once(
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
                        v___x_2766_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9,
                        );
                        lean_inc_ref(v_a_2739_);
                        v___x_2767_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2767_, 0, v_a_2739_);
                        lean_ctor_set(v___x_2767_, 1, v___x_2766_);
                        lean_inc(v_idx_2741_);
                        v___y_2743_ = v___x_2767_;
                        v_pos_2744_ = v_a_2739_;
                        v_idx_2745_ = v_idx_2741_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_array_2740_);
                        v_isSharedCheck_2778_ = (!lean_is_exclusive(v_a_2739_)) as u8;
                        if v_isSharedCheck_2778_ == 0 {
                            v_unused_2779_ = lean_ctor_get(v_a_2739_, 1);
                            lean_dec(v_unused_2779_);
                            v_unused_2780_ = lean_ctor_get(v_a_2739_, 0);
                            lean_dec(v_unused_2780_);
                            v___x_2769_ = v_a_2739_;
                            v_isShared_2770_ = v_isSharedCheck_2778_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_a_2739_);
                            v___x_2769_ = lean_box(0);
                            v_isShared_2770_ = v_isSharedCheck_2778_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2746_ = lean_nat_dec_eq(v_idx_2741_, v_idx_2745_);
                lean_dec(v_idx_2745_);
                lean_dec(v_idx_2741_);
                if v___x_2746_ == 0 {
                    lean_dec_ref(v_pos_2744_);
                    return v___y_2743_;
                } else {
                    lean_dec_ref(v___y_2743_);
                    v_utf8_2747_ = lean_obj_once(
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
                    if lean_obj_tag(v___x_2748_) == 0 {
                        v_pos_2749_ = lean_ctor_get(v___x_2748_, 0);
                        v_isSharedCheck_2757_ = (!lean_is_exclusive(v___x_2748_)) as u8;
                        if v_isSharedCheck_2757_ == 0 {
                            v_unused_2758_ = lean_ctor_get(v___x_2748_, 1);
                            lean_dec(v_unused_2758_);
                            v___x_2751_ = v___x_2748_;
                            v_isShared_2752_ = v_isSharedCheck_2757_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_pos_2749_);
                            lean_dec(v___x_2748_);
                            v___x_2751_ = lean_box(0);
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
                v___x_2753_ = lean_box(0);
                if v_isShared_2752_ == 0 {
                    lean_ctor_set(v___x_2751_, 1, v___x_2753_);
                    v___x_2755_ = v___x_2751_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_pos_2749_);
                    lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2753_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2755_;
            }
            4 => {
                v___x_2771_ = lean_unsigned_to_nat(1);
                v___x_2772_ = lean_nat_add(v_idx_2741_, v___x_2771_);
                lean_dec(v_idx_2741_);
                if v_isShared_2770_ == 0 {
                    lean_ctor_set(v___x_2769_, 1, v___x_2772_);
                    v___x_2774_ = v___x_2769_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_array_2740_);
                    lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2772_);
                    v___x_2774_ = v_reuseFailAlloc_2777_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2775_ = lean_box(0);
                v___x_2776_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2776_, 0, v___x_2774_);
                lean_ctor_set(v___x_2776_, 1, v___x_2775_);
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
    mut v_a_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2801_: u8 = 0;
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u32 = 0;
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2834_: u8 = 0;
    let mut v_unused_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2795_ = lean_ctor_get(v_a_2791_, 0);
                v_idx_2796_ = lean_ctor_get(v_a_2791_, 1);
                v___x_2797_ = lean_byte_array_size(v_array_2795_);
                v___x_2798_ = lean_nat_dec_lt(v_idx_2796_, v___x_2797_);
                if v___x_2798_ == 0 {
                    v___x_2799_ = lean_box(0);
                    v___x_2800_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2800_, 0, v_a_2791_);
                    lean_ctor_set(v___x_2800_, 1, v___x_2799_);
                    return v___x_2800_;
                } else {
                    v_c_2801_ = lean_byte_array_fget(v_array_2795_, v_idx_2796_);
                    v___x_2802_ = lean_uint8_once(
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
                        v___x_2804_ = lean_uint8_once(
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
                            lean_inc(v_idx_2796_);
                            lean_inc_ref(v_array_2795_);
                            v_isSharedCheck_2834_ = (!lean_is_exclusive(v_a_2791_)) as u8;
                            if v_isSharedCheck_2834_ == 0 {
                                v_unused_2835_ = lean_ctor_get(v_a_2791_, 1);
                                lean_dec(v_unused_2835_);
                                v_unused_2836_ = lean_ctor_get(v_a_2791_, 0);
                                lean_dec(v_unused_2836_);
                                v___x_2807_ = v_a_2791_;
                                v_isShared_2808_ = v_isSharedCheck_2834_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_2791_);
                                v___x_2807_ = lean_box(0);
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
                v___x_2794_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2794_, 0, v_a_2791_);
                lean_ctor_set(v___x_2794_, 1, v___x_2793_);
                return v___x_2794_;
            }
            2 => {
                v___x_2809_ = lean_unsigned_to_nat(1);
                v___x_2810_ = lean_nat_add(v_idx_2796_, v___x_2809_);
                lean_dec(v_idx_2796_);
                if v_isShared_2808_ == 0 {
                    lean_ctor_set(v___x_2807_, 1, v___x_2810_);
                    v_it_x27_2812_ = v___x_2807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_array_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2810_);
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
                v_fst_2818_ = lean_ctor_get(v___x_2817_, 0);
                v_snd_2819_ = lean_ctor_get(v___x_2817_, 1);
                v_isSharedCheck_2832_ = (!lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2832_ == 0 {
                    v___x_2821_ = v___x_2817_;
                    v_isShared_2822_ = v_isSharedCheck_2832_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2819_);
                    lean_inc(v_fst_2818_);
                    lean_dec(v___x_2817_);
                    v___x_2821_ = lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2823_ = lean_unsigned_to_nat(0);
                v___x_2824_ = lean_nat_dec_eq(v_fst_2818_, v___x_2823_);
                if v___x_2824_ == 0 {
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set(v___x_2821_, 1, v_fst_2818_);
                        lean_ctor_set(v___x_2821_, 0, v_snd_2819_);
                        v___x_2826_ = v___x_2821_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_snd_2819_);
                        lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_fst_2818_);
                        v___x_2826_ = v_reuseFailAlloc_2827_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_2818_);
                    v___x_2828_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set_tag(v___x_2821_, 1);
                        lean_ctor_set(v___x_2821_, 1, v___x_2828_);
                        lean_ctor_set(v___x_2821_, 0, v_snd_2819_);
                        v___x_2830_ = v___x_2821_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_snd_2819_);
                        lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2828_);
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
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1() -> *mut LeanObject
{
    let mut v___x_2839_: u8 = 0;
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    v___x_2839_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0,
    );
    v___x_2840_ = lean_uint8_to_nat(v___x_2839_);
    return v___x_2840_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2() -> *mut LeanObject
{
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    v___x_2841_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1,
    );
    v___x_2842_ = l_Nat_reprFast(v___x_2841_);
    return v___x_2842_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3() -> *mut LeanObject
{
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    v___x_2843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2,
    );
    v___x_2844_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_2845_ = lean_string_append(v___x_2844_, v___x_2843_);
    return v___x_2845_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4() -> *mut LeanObject
{
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    v___x_2846_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_2847_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3,
    );
    v___x_2848_ = lean_string_append(v___x_2847_, v___x_2846_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5() -> *mut LeanObject
{
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    v___x_2849_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4,
    );
    v___x_2850_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2850_, 0, v___x_2849_);
    return v___x_2850_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(
    mut v_a_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v_got_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2876_: u8 = 0;
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: u8 = 0;
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: u32 = 0;
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2892_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2904_: u8 = 0;
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_unused_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2852_ = lean_ctor_get(v_a_2851_, 0);
                v_idx_2853_ = lean_ctor_get(v_a_2851_, 1);
                v___x_2854_ = lean_byte_array_size(v_array_2852_);
                v___x_2855_ = lean_nat_dec_lt(v_idx_2853_, v___x_2854_);
                if v___x_2855_ == 0 {
                    v___x_2856_ = lean_box(0);
                    v___x_2857_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2857_, 0, v_a_2851_);
                    lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                    return v___x_2857_;
                } else {
                    v___x_2858_ = lean_uint8_once(
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
                        v___x_2861_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5,
                        );
                        v___x_2862_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2862_, 0, v_a_2851_);
                        lean_ctor_set(v___x_2862_, 1, v___x_2861_);
                        return v___x_2862_;
                    } else {
                        lean_inc(v_idx_2853_);
                        lean_inc_ref(v_array_2852_);
                        v_isSharedCheck_2906_ = (!lean_is_exclusive(v_a_2851_)) as u8;
                        if v_isSharedCheck_2906_ == 0 {
                            v_unused_2907_ = lean_ctor_get(v_a_2851_, 1);
                            lean_dec(v_unused_2907_);
                            v_unused_2908_ = lean_ctor_get(v_a_2851_, 0);
                            lean_dec(v_unused_2908_);
                            v___x_2864_ = v_a_2851_;
                            v_isShared_2865_ = v_isSharedCheck_2906_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2851_);
                            v___x_2864_ = lean_box(0);
                            v_isShared_2865_ = v_isSharedCheck_2906_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2866_ = lean_unsigned_to_nat(1);
                v___x_2867_ = lean_nat_add(v_idx_2853_, v___x_2866_);
                lean_dec(v_idx_2853_);
                lean_inc(v___x_2867_);
                lean_inc_ref(v_array_2852_);
                if v_isShared_2865_ == 0 {
                    lean_ctor_set(v___x_2864_, 1, v___x_2867_);
                    v___x_2869_ = v___x_2864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_array_2852_);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___x_2867_);
                    v___x_2869_ = v_reuseFailAlloc_2905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2873_ = lean_nat_dec_lt(v___x_2867_, v___x_2854_);
                if v___x_2873_ == 0 {
                    lean_dec(v___x_2867_);
                    lean_dec_ref(v_array_2852_);
                    v___x_2874_ = lean_box(0);
                    v___x_2875_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2875_, 0, v___x_2869_);
                    lean_ctor_set(v___x_2875_, 1, v___x_2874_);
                    return v___x_2875_;
                } else {
                    v_c_2876_ = lean_byte_array_fget(v_array_2852_, v___x_2867_);
                    v___x_2877_ = lean_uint8_once(
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
                        lean_dec(v___x_2867_);
                        lean_dec_ref(v_array_2852_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2879_ = lean_uint8_once(
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
                            lean_dec(v___x_2867_);
                            lean_dec_ref(v_array_2852_);
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v___x_2869_);
                            v___x_2881_ = lean_nat_add(v___x_2867_, v___x_2866_);
                            lean_dec(v___x_2867_);
                            v_it_x27_2882_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_it_x27_2882_, 0, v_array_2852_);
                            lean_ctor_set(v_it_x27_2882_, 1, v___x_2881_);
                            v___x_2883_ = lean_uint8_to_uint32(v_c_2876_);
                            v___x_2884_ = lean_uint32_to_uint8(v___x_2883_);
                            v___x_2885_ = lean_uint8_sub(v___x_2884_, v___x_2877_);
                            v___x_2886_ = lean_uint8_to_nat(v___x_2885_);
                            v___x_2887_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_2882_, v___x_2886_);
                            v_fst_2888_ = lean_ctor_get(v___x_2887_, 0);
                            v_snd_2889_ = lean_ctor_get(v___x_2887_, 1);
                            v_isSharedCheck_2904_ = (!lean_is_exclusive(v___x_2887_)) as u8;
                            if v_isSharedCheck_2904_ == 0 {
                                v___x_2891_ = v___x_2887_;
                                v_isShared_2892_ = v_isSharedCheck_2904_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_snd_2889_);
                                lean_inc(v_fst_2888_);
                                lean_dec(v___x_2887_);
                                v___x_2891_ = lean_box(0);
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
                v___x_2872_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2872_, 0, v___x_2869_);
                lean_ctor_set(v___x_2872_, 1, v___x_2871_);
                return v___x_2872_;
            }
            4 => {
                v___x_2893_ = lean_unsigned_to_nat(0);
                v___x_2894_ = lean_nat_dec_eq(v_fst_2888_, v___x_2893_);
                if v___x_2894_ == 0 {
                    v___x_2895_ = lean_nat_to_int(v_fst_2888_);
                    v___x_2896_ = lean_int_neg(v___x_2895_);
                    lean_dec(v___x_2895_);
                    if v_isShared_2892_ == 0 {
                        lean_ctor_set(v___x_2891_, 1, v___x_2896_);
                        lean_ctor_set(v___x_2891_, 0, v_snd_2889_);
                        v___x_2898_ = v___x_2891_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_snd_2889_);
                        lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2896_);
                        v___x_2898_ = v_reuseFailAlloc_2899_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_2888_);
                    v___x_2900_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_2892_ == 0 {
                        lean_ctor_set_tag(v___x_2891_, 1);
                        lean_ctor_set(v___x_2891_, 1, v___x_2900_);
                        lean_ctor_set(v___x_2891_, 0, v_snd_2889_);
                        v___x_2902_ = v___x_2891_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_snd_2889_);
                        lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2900_);
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
    mut v_a_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2919_: u8 = 0;
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u32 = 0;
    let mut v___x_2932_: u8 = 0;
    let mut v___x_2933_: u8 = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_reuseFailAlloc_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_unused_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2913_ = lean_ctor_get(v_a_2909_, 0);
                v_idx_2914_ = lean_ctor_get(v_a_2909_, 1);
                v___x_2915_ = lean_byte_array_size(v_array_2913_);
                v___x_2916_ = lean_nat_dec_lt(v_idx_2914_, v___x_2915_);
                if v___x_2916_ == 0 {
                    v___x_2917_ = lean_box(0);
                    v___x_2918_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2918_, 0, v_a_2909_);
                    lean_ctor_set(v___x_2918_, 1, v___x_2917_);
                    return v___x_2918_;
                } else {
                    v_c_2919_ = lean_byte_array_fget(v_array_2913_, v_idx_2914_);
                    v___x_2920_ = lean_uint8_once(
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
                        v___x_2922_ = lean_uint8_once(
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
                            lean_inc(v_idx_2914_);
                            lean_inc_ref(v_array_2913_);
                            v_isSharedCheck_2952_ = (!lean_is_exclusive(v_a_2909_)) as u8;
                            if v_isSharedCheck_2952_ == 0 {
                                v_unused_2953_ = lean_ctor_get(v_a_2909_, 1);
                                lean_dec(v_unused_2953_);
                                v_unused_2954_ = lean_ctor_get(v_a_2909_, 0);
                                lean_dec(v_unused_2954_);
                                v___x_2925_ = v_a_2909_;
                                v_isShared_2926_ = v_isSharedCheck_2952_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_2909_);
                                v___x_2925_ = lean_box(0);
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
                v___x_2912_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2912_, 0, v_a_2909_);
                lean_ctor_set(v___x_2912_, 1, v___x_2911_);
                return v___x_2912_;
            }
            2 => {
                v___x_2927_ = lean_unsigned_to_nat(1);
                v___x_2928_ = lean_nat_add(v_idx_2914_, v___x_2927_);
                lean_dec(v_idx_2914_);
                if v_isShared_2926_ == 0 {
                    lean_ctor_set(v___x_2925_, 1, v___x_2928_);
                    v_it_x27_2930_ = v___x_2925_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_array_2913_);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2928_);
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
                v_fst_2936_ = lean_ctor_get(v___x_2935_, 0);
                v_snd_2937_ = lean_ctor_get(v___x_2935_, 1);
                v_isSharedCheck_2950_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                if v_isSharedCheck_2950_ == 0 {
                    v___x_2939_ = v___x_2935_;
                    v_isShared_2940_ = v_isSharedCheck_2950_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2937_);
                    lean_inc(v_fst_2936_);
                    lean_dec(v___x_2935_);
                    v___x_2939_ = lean_box(0);
                    v_isShared_2940_ = v_isSharedCheck_2950_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2941_ = lean_unsigned_to_nat(0);
                v___x_2942_ = lean_nat_dec_eq(v_fst_2936_, v___x_2941_);
                if v___x_2942_ == 0 {
                    if v_isShared_2940_ == 0 {
                        lean_ctor_set(v___x_2939_, 1, v_fst_2936_);
                        lean_ctor_set(v___x_2939_, 0, v_snd_2937_);
                        v___x_2944_ = v___x_2939_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_snd_2937_);
                        lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_fst_2936_);
                        v___x_2944_ = v_reuseFailAlloc_2945_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_2936_);
                    v___x_2946_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_2940_ == 0 {
                        lean_ctor_set_tag(v___x_2939_, 1);
                        lean_ctor_set(v___x_2939_, 1, v___x_2946_);
                        lean_ctor_set(v___x_2939_, 0, v_snd_2937_);
                        v___x_2948_ = v___x_2939_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_snd_2937_);
                        lean_ctor_set(v_reuseFailAlloc_2949_, 1, v___x_2946_);
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
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0() -> *mut LeanObject
{
    let mut v___x_2955_: u8 = 0;
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2955_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2,
    );
    v___x_2956_ = lean_uint8_to_nat(v___x_2955_);
    return v___x_2956_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1() -> *mut LeanObject
{
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    v___x_2957_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0,
    );
    v___x_2958_ = l_Nat_reprFast(v___x_2957_);
    return v___x_2958_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2() -> *mut LeanObject
{
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1,
    );
    v___x_2960_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_2961_ = lean_string_append(v___x_2960_, v___x_2959_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3() -> *mut LeanObject
{
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_2963_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2,
    );
    v___x_2964_ = lean_string_append(v___x_2963_, v___x_2962_);
    return v___x_2964_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4() -> *mut LeanObject
{
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    v___x_2965_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3,
    );
    v___x_2966_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2966_, 0, v___x_2965_);
    return v___x_2966_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(
    mut v_a_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut v_got_2975_: u8 = 0;
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_unused_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2968_ = lean_ctor_get(v_a_2967_, 0);
                v_idx_2969_ = lean_ctor_get(v_a_2967_, 1);
                v___x_2970_ = lean_byte_array_size(v_array_2968_);
                v___x_2971_ = lean_nat_dec_lt(v_idx_2969_, v___x_2970_);
                if v___x_2971_ == 0 {
                    v___x_2972_ = lean_box(0);
                    v___x_2973_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2973_, 0, v_a_2967_);
                    lean_ctor_set(v___x_2973_, 1, v___x_2972_);
                    return v___x_2973_;
                } else {
                    v___x_2974_ = lean_uint8_once(
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
                        v___x_2977_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        v___x_2978_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2978_, 0, v_a_2967_);
                        lean_ctor_set(v___x_2978_, 1, v___x_2977_);
                        return v___x_2978_;
                    } else {
                        lean_inc(v_idx_2969_);
                        lean_inc_ref(v_array_2968_);
                        v_isSharedCheck_2989_ = (!lean_is_exclusive(v_a_2967_)) as u8;
                        if v_isSharedCheck_2989_ == 0 {
                            v_unused_2990_ = lean_ctor_get(v_a_2967_, 1);
                            lean_dec(v_unused_2990_);
                            v_unused_2991_ = lean_ctor_get(v_a_2967_, 0);
                            lean_dec(v_unused_2991_);
                            v___x_2980_ = v_a_2967_;
                            v_isShared_2981_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2967_);
                            v___x_2980_ = lean_box(0);
                            v_isShared_2981_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2982_ = lean_unsigned_to_nat(1);
                v___x_2983_ = lean_nat_add(v_idx_2969_, v___x_2982_);
                lean_dec(v_idx_2969_);
                if v_isShared_2981_ == 0 {
                    lean_ctor_set(v___x_2980_, 1, v___x_2983_);
                    v___x_2985_ = v___x_2980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_array_2968_);
                    lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2983_);
                    v___x_2985_ = v_reuseFailAlloc_2988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2986_ = lean_box(0);
                v___x_2987_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2987_, 0, v___x_2985_);
                lean_ctor_set(v___x_2987_, 1, v___x_2986_);
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
-> *mut LeanObject {
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    v___x_2994_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
    v___x_2995_ = lean_uint8_to_nat(v___x_2994_);
    return v___x_2995_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2()
-> *mut LeanObject {
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    v___x_2996_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1);
    v___x_2997_ = l_Nat_reprFast(v___x_2996_);
    return v___x_2997_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3()
-> *mut LeanObject {
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    v___x_2998_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2);
    v___x_2999_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
    v___x_3000_ = lean_string_append(v___x_2999_, v___x_2998_);
    return v___x_3000_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4()
-> *mut LeanObject {
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    v___x_3001_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_3002_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3);
    v___x_3003_ = lean_string_append(v___x_3002_, v___x_3001_);
    return v___x_3003_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5()
-> *mut LeanObject {
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    v___x_3004_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4);
    v___x_3005_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3005_, 0, v___x_3004_);
    return v___x_3005_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(
    mut v_a_3006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: u8 = 0;
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u32 = 0;
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: u8 = 0;
    let mut v_array_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    let mut v_got_3045_: u8 = 0;
    let mut v___x_3046_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_unused_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3010_ = lean_ctor_get(v_a_3006_, 0);
                v_idx_3011_ = lean_ctor_get(v_a_3006_, 1);
                v___x_3012_ = lean_byte_array_size(v_array_3010_);
                v___x_3013_ = lean_nat_dec_lt(v_idx_3011_, v___x_3012_);
                if v___x_3013_ == 0 {
                    v___x_3014_ = lean_box(0);
                    v___x_3015_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3015_, 0, v_a_3006_);
                    lean_ctor_set(v___x_3015_, 1, v___x_3014_);
                    return v___x_3015_;
                } else {
                    v_c_3016_ = lean_byte_array_fget(v_array_3010_, v_idx_3011_);
                    v___x_3017_ = lean_uint8_once(
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
                        v___x_3019_ = lean_uint8_once(
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
                            v___x_3021_ = lean_unsigned_to_nat(1);
                            v___x_3022_ = lean_nat_add(v_idx_3011_, v___x_3021_);
                            lean_inc_ref(v_array_3010_);
                            v_it_x27_3023_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_it_x27_3023_, 0, v_array_3010_);
                            lean_ctor_set(v_it_x27_3023_, 1, v___x_3022_);
                            v___x_3024_ = lean_uint8_to_uint32(v_c_3016_);
                            v___x_3025_ = lean_uint32_to_uint8(v___x_3024_);
                            v___x_3026_ = lean_uint8_sub(v___x_3025_, v___x_3017_);
                            v___x_3027_ = lean_uint8_to_nat(v___x_3026_);
                            v___x_3028_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3023_, v___x_3027_);
                            v_fst_3029_ = lean_ctor_get(v___x_3028_, 0);
                            v_snd_3030_ = lean_ctor_get(v___x_3028_, 1);
                            v_isSharedCheck_3068_ = (!lean_is_exclusive(v___x_3028_)) as u8;
                            if v_isSharedCheck_3068_ == 0 {
                                v___x_3032_ = v___x_3028_;
                                v_isShared_3033_ = v_isSharedCheck_3068_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_snd_3030_);
                                lean_inc(v_fst_3029_);
                                lean_dec(v___x_3028_);
                                v___x_3032_ = lean_box(0);
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
                v___x_3009_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3009_, 0, v_a_3006_);
                lean_ctor_set(v___x_3009_, 1, v___x_3008_);
                return v___x_3009_;
            }
            2 => {
                v___x_3034_ = lean_unsigned_to_nat(0);
                v___x_3035_ = lean_nat_dec_eq(v_fst_3029_, v___x_3034_);
                if v___x_3035_ == 0 {
                    lean_dec_ref(v_a_3006_);
                    v_array_3036_ = lean_ctor_get(v_snd_3030_, 0);
                    v_idx_3037_ = lean_ctor_get(v_snd_3030_, 1);
                    v___x_3038_ = lean_byte_array_size(v_array_3036_);
                    v___x_3039_ = lean_nat_dec_lt(v_idx_3037_, v___x_3038_);
                    if v___x_3039_ == 0 {
                        lean_dec(v_fst_3029_);
                        v___x_3040_ = lean_box(0);
                        if v_isShared_3033_ == 0 {
                            lean_ctor_set_tag(v___x_3032_, 1);
                            lean_ctor_set(v___x_3032_, 1, v___x_3040_);
                            lean_ctor_set(v___x_3032_, 0, v_snd_3030_);
                            v___x_3042_ = v___x_3032_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_snd_3030_);
                            lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3040_);
                            v___x_3042_ = v_reuseFailAlloc_3043_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3044_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                        v_got_3045_ = lean_byte_array_fget(v_array_3036_, v_idx_3037_);
                        v___x_3046_ = lean_uint8_dec_eq(v_got_3045_, v___x_3044_);
                        if v___x_3046_ == 0 {
                            lean_dec(v_fst_3029_);
                            v___x_3047_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                            if v_isShared_3033_ == 0 {
                                lean_ctor_set_tag(v___x_3032_, 1);
                                lean_ctor_set(v___x_3032_, 1, v___x_3047_);
                                lean_ctor_set(v___x_3032_, 0, v_snd_3030_);
                                v___x_3049_ = v___x_3032_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_snd_3030_);
                                lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3047_);
                                v___x_3049_ = v_reuseFailAlloc_3050_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_inc(v_idx_3037_);
                            lean_inc_ref(v_array_3036_);
                            v_isSharedCheck_3061_ = (!lean_is_exclusive(v_snd_3030_)) as u8;
                            if v_isSharedCheck_3061_ == 0 {
                                v_unused_3062_ = lean_ctor_get(v_snd_3030_, 1);
                                lean_dec(v_unused_3062_);
                                v_unused_3063_ = lean_ctor_get(v_snd_3030_, 0);
                                lean_dec(v_unused_3063_);
                                v___x_3052_ = v_snd_3030_;
                                v_isShared_3053_ = v_isSharedCheck_3061_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v_snd_3030_);
                                v___x_3052_ = lean_box(0);
                                v_isShared_3053_ = v_isSharedCheck_3061_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_snd_3030_);
                    lean_dec(v_fst_3029_);
                    v___x_3064_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3033_ == 0 {
                        lean_ctor_set_tag(v___x_3032_, 1);
                        lean_ctor_set(v___x_3032_, 1, v___x_3064_);
                        lean_ctor_set(v___x_3032_, 0, v_a_3006_);
                        v___x_3066_ = v___x_3032_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3006_);
                        lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3064_);
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
                lean_dec(v_idx_3037_);
                if v_isShared_3053_ == 0 {
                    lean_ctor_set(v___x_3052_, 1, v___x_3054_);
                    v___x_3056_ = v___x_3052_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_array_3036_);
                    lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3054_);
                    v___x_3056_ = v_reuseFailAlloc_3060_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3033_ == 0 {
                    lean_ctor_set(v___x_3032_, 1, v_fst_3029_);
                    lean_ctor_set(v___x_3032_, 0, v___x_3056_);
                    v___x_3058_ = v___x_3032_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
                    lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_fst_3029_);
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
    mut v_acc_3069_: *mut LeanObject,
    mut v_a_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3085_: u8 = 0;
    let mut v___x_3086_: u8 = 0;
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: u8 = 0;
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u32 = 0;
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v_array_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v_got_3108_: u8 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3113_: u8 = 0;
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v_unused_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3071_ = lean_ctor_get(v_a_3070_, 0);
                v_idx_3072_ = lean_ctor_get(v_a_3070_, 1);
                lean_inc(v_idx_3072_);
                v___x_3082_ = lean_byte_array_size(v_array_3071_);
                v___x_3083_ = lean_nat_dec_lt(v_idx_3072_, v___x_3082_);
                if v___x_3083_ == 0 {
                    v___x_3084_ = lean_box(0);
                    lean_inc(v_idx_3072_);
                    v_pos_3074_ = v_a_3070_;
                    v_idx_3075_ = v_idx_3072_;
                    v_err_3076_ = v___x_3084_;
                    state = 1;
                    continue;
                } else {
                    v_c_3085_ = lean_byte_array_fget(v_array_3071_, v_idx_3072_);
                    v___x_3086_ = lean_uint8_once(
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
                        v___x_3088_ = lean_uint8_once(
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
                            v___x_3090_ = lean_unsigned_to_nat(1);
                            v___x_3091_ = lean_nat_add(v_idx_3072_, v___x_3090_);
                            lean_inc_ref(v_array_3071_);
                            v_it_x27_3092_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_it_x27_3092_, 0, v_array_3071_);
                            lean_ctor_set(v_it_x27_3092_, 1, v___x_3091_);
                            v___x_3093_ = lean_uint8_to_uint32(v_c_3085_);
                            v___x_3094_ = lean_uint32_to_uint8(v___x_3093_);
                            v___x_3095_ = lean_uint8_sub(v___x_3094_, v___x_3086_);
                            v___x_3096_ = lean_uint8_to_nat(v___x_3095_);
                            v___x_3097_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3092_, v___x_3096_);
                            v_fst_3098_ = lean_ctor_get(v___x_3097_, 0);
                            lean_inc(v_fst_3098_);
                            v_snd_3099_ = lean_ctor_get(v___x_3097_, 1);
                            lean_inc(v_snd_3099_);
                            lean_dec_ref(v___x_3097_);
                            v___x_3100_ = lean_unsigned_to_nat(0);
                            v___x_3101_ = lean_nat_dec_eq(v_fst_3098_, v___x_3100_);
                            if v___x_3101_ == 0 {
                                lean_dec_ref(v_a_3070_);
                                v_array_3102_ = lean_ctor_get(v_snd_3099_, 0);
                                v_idx_3103_ = lean_ctor_get(v_snd_3099_, 1);
                                lean_inc(v_idx_3103_);
                                v___x_3104_ = lean_byte_array_size(v_array_3102_);
                                v___x_3105_ = lean_nat_dec_lt(v_idx_3103_, v___x_3104_);
                                if v___x_3105_ == 0 {
                                    lean_dec(v_fst_3098_);
                                    v___x_3106_ = lean_box(0);
                                    v_pos_3074_ = v_snd_3099_;
                                    v_idx_3075_ = v_idx_3103_;
                                    v_err_3076_ = v___x_3106_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3107_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                                    v_got_3108_ = lean_byte_array_fget(v_array_3102_, v_idx_3103_);
                                    v___x_3109_ = lean_uint8_dec_eq(v_got_3108_, v___x_3107_);
                                    if v___x_3109_ == 0 {
                                        lean_dec(v_fst_3098_);
                                        v___x_3110_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                                        v_pos_3074_ = v_snd_3099_;
                                        v_idx_3075_ = v_idx_3103_;
                                        v_err_3076_ = v___x_3110_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc_ref(v_array_3102_);
                                        lean_dec(v_idx_3072_);
                                        v_isSharedCheck_3120_ =
                                            (!lean_is_exclusive(v_snd_3099_)) as u8;
                                        if v_isSharedCheck_3120_ == 0 {
                                            v_unused_3121_ = lean_ctor_get(v_snd_3099_, 1);
                                            lean_dec(v_unused_3121_);
                                            v_unused_3122_ = lean_ctor_get(v_snd_3099_, 0);
                                            lean_dec(v_unused_3122_);
                                            v___x_3112_ = v_snd_3099_;
                                            v_isShared_3113_ = v_isSharedCheck_3120_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_dec(v_snd_3099_);
                                            v___x_3112_ = lean_box(0);
                                            v_isShared_3113_ = v_isSharedCheck_3120_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_snd_3099_);
                                lean_dec(v_fst_3098_);
                                v___x_3123_ =
                                    l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                                lean_inc(v_idx_3072_);
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
                lean_dec(v_idx_3075_);
                lean_dec(v_idx_3072_);
                if v___x_3077_ == 0 {
                    lean_dec_ref(v_acc_3069_);
                    lean_inc(v_err_3076_);
                    v___x_3078_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3078_, 0, v_pos_3074_);
                    lean_ctor_set(v___x_3078_, 1, v_err_3076_);
                    return v___x_3078_;
                } else {
                    v___x_3079_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3079_, 0, v_pos_3074_);
                    lean_ctor_set(v___x_3079_, 1, v_acc_3069_);
                    return v___x_3079_;
                }
            }
            2 => {
                v___x_3081_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                lean_inc(v_idx_3072_);
                v_pos_3074_ = v_a_3070_;
                v_idx_3075_ = v_idx_3072_;
                v_err_3076_ = v___x_3081_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3114_ = lean_nat_add(v_idx_3103_, v___x_3090_);
                lean_dec(v_idx_3103_);
                if v_isShared_3113_ == 0 {
                    lean_ctor_set(v___x_3112_, 1, v___x_3114_);
                    v___x_3116_ = v___x_3112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_array_3102_);
                    lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3114_);
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
    mut v_a_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ = lean_uint8_once(
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
-> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    v___x_3135_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    v___x_3138_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_3139_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    v___x_3141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4,
    );
    v___x_3142_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3142_, 0, v___x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(
    mut v_a_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: u8 = 0;
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v_got_3151_: u8 = 0;
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v_got_3166_: u8 = 0;
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v_array_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v_got_3187_: u8 = 0;
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut v_unused_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut v_pos_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut v_reuseFailAlloc_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut v_unused_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3144_ = lean_ctor_get(v_a_3143_, 0);
                v_idx_3145_ = lean_ctor_get(v_a_3143_, 1);
                v___x_3146_ = lean_byte_array_size(v_array_3144_);
                v___x_3147_ = lean_nat_dec_lt(v_idx_3145_, v___x_3146_);
                if v___x_3147_ == 0 {
                    v___x_3148_ = lean_box(0);
                    v___x_3149_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3149_, 0, v_a_3143_);
                    lean_ctor_set(v___x_3149_, 1, v___x_3148_);
                    return v___x_3149_;
                } else {
                    v___x_3150_ = lean_uint8_once(
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
                        v___x_3153_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5,
                        );
                        v___x_3154_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3154_, 0, v_a_3143_);
                        lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                        return v___x_3154_;
                    } else {
                        lean_inc(v_idx_3145_);
                        lean_inc_ref(v_array_3144_);
                        v_isSharedCheck_3218_ = (!lean_is_exclusive(v_a_3143_)) as u8;
                        if v_isSharedCheck_3218_ == 0 {
                            v_unused_3219_ = lean_ctor_get(v_a_3143_, 1);
                            lean_dec(v_unused_3219_);
                            v_unused_3220_ = lean_ctor_get(v_a_3143_, 0);
                            lean_dec(v_unused_3220_);
                            v___x_3156_ = v_a_3143_;
                            v_isShared_3157_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3143_);
                            v___x_3156_ = lean_box(0);
                            v_isShared_3157_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3158_ = lean_unsigned_to_nat(1);
                v___x_3159_ = lean_nat_add(v_idx_3145_, v___x_3158_);
                lean_dec(v_idx_3145_);
                lean_inc(v___x_3159_);
                lean_inc_ref(v_array_3144_);
                if v_isShared_3157_ == 0 {
                    lean_ctor_set(v___x_3156_, 1, v___x_3159_);
                    v___x_3161_ = v___x_3156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_array_3144_);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3159_);
                    v___x_3161_ = v_reuseFailAlloc_3217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3162_ = lean_nat_dec_lt(v___x_3159_, v___x_3146_);
                if v___x_3162_ == 0 {
                    lean_dec(v___x_3159_);
                    lean_dec_ref(v_array_3144_);
                    v___x_3163_ = lean_box(0);
                    v___x_3164_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3164_, 0, v___x_3161_);
                    lean_ctor_set(v___x_3164_, 1, v___x_3163_);
                    return v___x_3164_;
                } else {
                    v___x_3165_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3166_ = lean_byte_array_fget(v_array_3144_, v___x_3159_);
                    v___x_3167_ = lean_uint8_dec_eq(v_got_3166_, v___x_3165_);
                    if v___x_3167_ == 0 {
                        lean_dec(v___x_3159_);
                        lean_dec_ref(v_array_3144_);
                        v___x_3168_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        v___x_3169_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3169_, 0, v___x_3161_);
                        lean_ctor_set(v___x_3169_, 1, v___x_3168_);
                        return v___x_3169_;
                    } else {
                        lean_dec_ref(v___x_3161_);
                        v___x_3170_ = lean_nat_add(v___x_3159_, v___x_3158_);
                        lean_dec(v___x_3159_);
                        v___x_3171_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3171_, 0, v_array_3144_);
                        lean_ctor_set(v___x_3171_, 1, v___x_3170_);
                        v___x_3172_ =
                            l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_3171_);
                        if lean_obj_tag(v___x_3172_) == 0 {
                            v_pos_3173_ = lean_ctor_get(v___x_3172_, 0);
                            v_res_3174_ = lean_ctor_get(v___x_3172_, 1);
                            v_isSharedCheck_3207_ = (!lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3207_ == 0 {
                                v___x_3176_ = v___x_3172_;
                                v_isShared_3177_ = v_isSharedCheck_3207_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_res_3174_);
                                lean_inc(v_pos_3173_);
                                lean_dec(v___x_3172_);
                                v___x_3176_ = lean_box(0);
                                v_isShared_3177_ = v_isSharedCheck_3207_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_pos_3208_ = lean_ctor_get(v___x_3172_, 0);
                            v_err_3209_ = lean_ctor_get(v___x_3172_, 1);
                            v_isSharedCheck_3216_ = (!lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3216_ == 0 {
                                v___x_3211_ = v___x_3172_;
                                v_isShared_3212_ = v_isSharedCheck_3216_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_err_3209_);
                                lean_inc(v_pos_3208_);
                                lean_dec(v___x_3172_);
                                v___x_3211_ = lean_box(0);
                                v_isShared_3212_ = v_isSharedCheck_3216_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v_array_3178_ = lean_ctor_get(v_pos_3173_, 0);
                v_idx_3179_ = lean_ctor_get(v_pos_3173_, 1);
                v___x_3180_ = lean_byte_array_size(v_array_3178_);
                v___x_3181_ = lean_nat_dec_lt(v_idx_3179_, v___x_3180_);
                if v___x_3181_ == 0 {
                    lean_dec(v_res_3174_);
                    v___x_3182_ = lean_box(0);
                    if v_isShared_3177_ == 0 {
                        lean_ctor_set_tag(v___x_3176_, 1);
                        lean_ctor_set(v___x_3176_, 1, v___x_3182_);
                        v___x_3184_ = v___x_3176_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_pos_3173_);
                        lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_3182_);
                        v___x_3184_ = v_reuseFailAlloc_3185_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3186_ = lean_uint8_once(
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
                        lean_dec(v_res_3174_);
                        v___x_3189_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        if v_isShared_3177_ == 0 {
                            lean_ctor_set_tag(v___x_3176_, 1);
                            lean_ctor_set(v___x_3176_, 1, v___x_3189_);
                            v___x_3191_ = v___x_3176_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_pos_3173_);
                            lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3189_);
                            v___x_3191_ = v_reuseFailAlloc_3192_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_3179_);
                        lean_inc_ref(v_array_3178_);
                        v_isSharedCheck_3204_ = (!lean_is_exclusive(v_pos_3173_)) as u8;
                        if v_isSharedCheck_3204_ == 0 {
                            v_unused_3205_ = lean_ctor_get(v_pos_3173_, 1);
                            lean_dec(v_unused_3205_);
                            v_unused_3206_ = lean_ctor_get(v_pos_3173_, 0);
                            lean_dec(v_unused_3206_);
                            v___x_3194_ = v_pos_3173_;
                            v_isShared_3195_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_pos_3173_);
                            v___x_3194_ = lean_box(0);
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
                lean_dec(v_idx_3179_);
                if v_isShared_3195_ == 0 {
                    lean_ctor_set(v___x_3194_, 1, v___x_3196_);
                    v___x_3198_ = v___x_3194_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_array_3178_);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3196_);
                    v___x_3198_ = v_reuseFailAlloc_3203_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3199_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3199_, 0, v_res_3174_);
                if v_isShared_3177_ == 0 {
                    lean_ctor_set(v___x_3176_, 1, v___x_3199_);
                    lean_ctor_set(v___x_3176_, 0, v___x_3198_);
                    v___x_3201_ = v___x_3176_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3198_);
                    lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3199_);
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
                    v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_pos_3208_);
                    lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_err_3209_);
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
    mut v_a_3221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: u8 = 0;
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3242_: u8 = 0;
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u32 = 0;
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_reuseFailAlloc_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_unused_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3289_: u8 = 0;
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u32 = 0;
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_unused_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3225_ = lean_ctor_get(v_a_3221_, 0);
                v_idx_3226_ = lean_ctor_get(v_a_3221_, 1);
                v___x_3227_ = lean_byte_array_size(v_array_3225_);
                v___x_3228_ = lean_nat_dec_lt(v_idx_3226_, v___x_3227_);
                if v___x_3228_ == 0 {
                    v___x_3229_ = lean_box(0);
                    v___x_3230_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3230_, 0, v_a_3221_);
                    lean_ctor_set(v___x_3230_, 1, v___x_3229_);
                    return v___x_3230_;
                } else {
                    v___x_3231_ = lean_byte_array_fget(v_array_3225_, v_idx_3226_);
                    v___x_3232_ = lean_uint8_once(
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
                            v___x_3234_ = lean_box(0);
                            v___x_3235_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3235_, 0, v_a_3221_);
                            lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                            return v___x_3235_;
                        } else {
                            v___x_3236_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                            v___x_3237_ = lean_uint8_dec_le(v___x_3236_, v___x_3231_);
                            if v___x_3237_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_3238_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                v___x_3239_ = lean_uint8_dec_le(v___x_3231_, v___x_3238_);
                                if v___x_3239_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_idx_3226_);
                                    lean_inc_ref(v_array_3225_);
                                    v_isSharedCheck_3269_ = (!lean_is_exclusive(v_a_3221_)) as u8;
                                    if v_isSharedCheck_3269_ == 0 {
                                        v_unused_3270_ = lean_ctor_get(v_a_3221_, 1);
                                        lean_dec(v_unused_3270_);
                                        v_unused_3271_ = lean_ctor_get(v_a_3221_, 0);
                                        lean_dec(v_unused_3271_);
                                        v___x_3241_ = v_a_3221_;
                                        v_isShared_3242_ = v_isSharedCheck_3269_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_a_3221_);
                                        v___x_3241_ = lean_box(0);
                                        v_isShared_3242_ = v_isSharedCheck_3269_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_3228_ == 0 {
                            v___x_3272_ = lean_box(0);
                            v___x_3273_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3273_, 0, v_a_3221_);
                            lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                            return v___x_3273_;
                        } else {
                            if v___x_3233_ == 0 {
                                v___x_3274_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
                                v___x_3275_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3275_, 0, v_a_3221_);
                                lean_ctor_set(v___x_3275_, 1, v___x_3274_);
                                return v___x_3275_;
                            } else {
                                lean_inc(v_idx_3226_);
                                lean_inc_ref(v_array_3225_);
                                v_isSharedCheck_3319_ = (!lean_is_exclusive(v_a_3221_)) as u8;
                                if v_isSharedCheck_3319_ == 0 {
                                    v_unused_3320_ = lean_ctor_get(v_a_3221_, 1);
                                    lean_dec(v_unused_3320_);
                                    v_unused_3321_ = lean_ctor_get(v_a_3221_, 0);
                                    lean_dec(v_unused_3321_);
                                    v___x_3277_ = v_a_3221_;
                                    v_isShared_3278_ = v_isSharedCheck_3319_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec(v_a_3221_);
                                    v___x_3277_ = lean_box(0);
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
                v___x_3224_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3224_, 0, v_a_3221_);
                lean_ctor_set(v___x_3224_, 1, v___x_3223_);
                return v___x_3224_;
            }
            2 => {
                v___x_3243_ = lean_unsigned_to_nat(1);
                v___x_3244_ = lean_nat_add(v_idx_3226_, v___x_3243_);
                lean_dec(v_idx_3226_);
                if v_isShared_3242_ == 0 {
                    lean_ctor_set(v___x_3241_, 1, v___x_3244_);
                    v_it_x27_3246_ = v___x_3241_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_array_3225_);
                    lean_ctor_set(v_reuseFailAlloc_3268_, 1, v___x_3244_);
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
                v_fst_3252_ = lean_ctor_get(v___x_3251_, 0);
                v_snd_3253_ = lean_ctor_get(v___x_3251_, 1);
                v_isSharedCheck_3267_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                if v_isSharedCheck_3267_ == 0 {
                    v___x_3255_ = v___x_3251_;
                    v_isShared_3256_ = v_isSharedCheck_3267_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_3253_);
                    lean_inc(v_fst_3252_);
                    lean_dec(v___x_3251_);
                    v___x_3255_ = lean_box(0);
                    v_isShared_3256_ = v_isSharedCheck_3267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3257_ = lean_unsigned_to_nat(0);
                v___x_3258_ = lean_nat_dec_eq(v_fst_3252_, v___x_3257_);
                if v___x_3258_ == 0 {
                    v___x_3259_ = lean_nat_to_int(v_fst_3252_);
                    if v_isShared_3256_ == 0 {
                        lean_ctor_set(v___x_3255_, 1, v___x_3259_);
                        lean_ctor_set(v___x_3255_, 0, v_snd_3253_);
                        v___x_3261_ = v___x_3255_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_snd_3253_);
                        lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3259_);
                        v___x_3261_ = v_reuseFailAlloc_3262_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_3252_);
                    v___x_3263_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3256_ == 0 {
                        lean_ctor_set_tag(v___x_3255_, 1);
                        lean_ctor_set(v___x_3255_, 1, v___x_3263_);
                        lean_ctor_set(v___x_3255_, 0, v_snd_3253_);
                        v___x_3265_ = v___x_3255_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_snd_3253_);
                        lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
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
                v___x_3279_ = lean_unsigned_to_nat(1);
                v___x_3280_ = lean_nat_add(v_idx_3226_, v___x_3279_);
                lean_dec(v_idx_3226_);
                lean_inc(v___x_3280_);
                lean_inc_ref(v_array_3225_);
                if v_isShared_3278_ == 0 {
                    lean_ctor_set(v___x_3277_, 1, v___x_3280_);
                    v___x_3282_ = v___x_3277_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_array_3225_);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3318_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3286_ = lean_nat_dec_lt(v___x_3280_, v___x_3227_);
                if v___x_3286_ == 0 {
                    lean_dec(v___x_3280_);
                    lean_dec_ref(v_array_3225_);
                    v___x_3287_ = lean_box(0);
                    v___x_3288_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3288_, 0, v___x_3282_);
                    lean_ctor_set(v___x_3288_, 1, v___x_3287_);
                    return v___x_3288_;
                } else {
                    v_c_3289_ = lean_byte_array_fget(v_array_3225_, v___x_3280_);
                    v___x_3290_ = lean_uint8_once(
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
                        lean_dec(v___x_3280_);
                        lean_dec_ref(v_array_3225_);
                        state = 9;
                        continue;
                    } else {
                        v___x_3292_ = lean_uint8_once(
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
                            lean_dec(v___x_3280_);
                            lean_dec_ref(v_array_3225_);
                            state = 9;
                            continue;
                        } else {
                            lean_dec_ref(v___x_3282_);
                            v___x_3294_ = lean_nat_add(v___x_3280_, v___x_3279_);
                            lean_dec(v___x_3280_);
                            v_it_x27_3295_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_it_x27_3295_, 0, v_array_3225_);
                            lean_ctor_set(v_it_x27_3295_, 1, v___x_3294_);
                            v___x_3296_ = lean_uint8_to_uint32(v_c_3289_);
                            v___x_3297_ = lean_uint32_to_uint8(v___x_3296_);
                            v___x_3298_ = lean_uint8_sub(v___x_3297_, v___x_3290_);
                            v___x_3299_ = lean_uint8_to_nat(v___x_3298_);
                            v___x_3300_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3295_, v___x_3299_);
                            v_fst_3301_ = lean_ctor_get(v___x_3300_, 0);
                            v_snd_3302_ = lean_ctor_get(v___x_3300_, 1);
                            v_isSharedCheck_3317_ = (!lean_is_exclusive(v___x_3300_)) as u8;
                            if v_isSharedCheck_3317_ == 0 {
                                v___x_3304_ = v___x_3300_;
                                v_isShared_3305_ = v_isSharedCheck_3317_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_3302_);
                                lean_inc(v_fst_3301_);
                                lean_dec(v___x_3300_);
                                v___x_3304_ = lean_box(0);
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
                v___x_3285_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3285_, 0, v___x_3282_);
                lean_ctor_set(v___x_3285_, 1, v___x_3284_);
                return v___x_3285_;
            }
            10 => {
                v___x_3306_ = lean_unsigned_to_nat(0);
                v___x_3307_ = lean_nat_dec_eq(v_fst_3301_, v___x_3306_);
                if v___x_3307_ == 0 {
                    v___x_3308_ = lean_nat_to_int(v_fst_3301_);
                    v___x_3309_ = lean_int_neg(v___x_3308_);
                    lean_dec(v___x_3308_);
                    if v_isShared_3305_ == 0 {
                        lean_ctor_set(v___x_3304_, 1, v___x_3309_);
                        lean_ctor_set(v___x_3304_, 0, v_snd_3302_);
                        v___x_3311_ = v___x_3304_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_snd_3302_);
                        lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3309_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_3301_);
                    v___x_3313_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3305_ == 0 {
                        lean_ctor_set_tag(v___x_3304_, 1);
                        lean_ctor_set(v___x_3304_, 1, v___x_3313_);
                        lean_ctor_set(v___x_3304_, 0, v_snd_3302_);
                        v___x_3315_ = v___x_3304_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_snd_3302_);
                        lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3313_);
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
    mut v_a_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v_got_3333_: u8 = 0;
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: u8 = 0;
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: u8 = 0;
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3369_: u8 = 0;
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: u32 = 0;
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3400_: u8 = 0;
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: u8 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u32 = 0;
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: u8 = 0;
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3355_ = lean_ctor_get(v_a_3322_, 0);
                v_idx_3356_ = lean_ctor_get(v_a_3322_, 1);
                v___x_3357_ = lean_byte_array_size(v_array_3355_);
                v___x_3358_ = lean_nat_dec_lt(v_idx_3356_, v___x_3357_);
                if v___x_3358_ == 0 {
                    v___x_3359_ = lean_box(0);
                    v___x_3360_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3360_, 0, v_a_3322_);
                    lean_ctor_set(v___x_3360_, 1, v___x_3359_);
                    return v___x_3360_;
                } else {
                    v___x_3361_ = lean_byte_array_fget(v_array_3355_, v_idx_3356_);
                    v___x_3362_ = lean_uint8_once(
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
                            v___x_3364_ = lean_box(0);
                            v___x_3365_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3365_, 0, v_a_3322_);
                            lean_ctor_set(v___x_3365_, 1, v___x_3364_);
                            return v___x_3365_;
                        } else {
                            v___x_3366_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                            v___x_3367_ = lean_uint8_dec_le(v___x_3366_, v___x_3361_);
                            if v___x_3367_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v___x_3368_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                v___x_3369_ = lean_uint8_dec_le(v___x_3361_, v___x_3368_);
                                if v___x_3369_ == 0 {
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_3370_ = lean_unsigned_to_nat(1);
                                    v___x_3371_ = lean_nat_add(v_idx_3356_, v___x_3370_);
                                    lean_inc_ref(v_array_3355_);
                                    v_it_x27_3372_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_it_x27_3372_, 0, v_array_3355_);
                                    lean_ctor_set(v_it_x27_3372_, 1, v___x_3371_);
                                    v___x_3373_ = lean_uint8_to_uint32(v___x_3361_);
                                    v___x_3374_ = lean_uint32_to_uint8(v___x_3373_);
                                    v___x_3375_ = lean_uint8_sub(v___x_3374_, v___x_3366_);
                                    v___x_3376_ = lean_uint8_to_nat(v___x_3375_);
                                    v___x_3377_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3372_, v___x_3376_);
                                    v_fst_3378_ = lean_ctor_get(v___x_3377_, 0);
                                    v_snd_3379_ = lean_ctor_get(v___x_3377_, 1);
                                    v_isSharedCheck_3390_ = (!lean_is_exclusive(v___x_3377_)) as u8;
                                    if v_isSharedCheck_3390_ == 0 {
                                        v___x_3381_ = v___x_3377_;
                                        v_isShared_3382_ = v_isSharedCheck_3390_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_3379_);
                                        lean_inc(v_fst_3378_);
                                        lean_dec(v___x_3377_);
                                        v___x_3381_ = lean_box(0);
                                        v_isShared_3382_ = v_isSharedCheck_3390_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        if v___x_3358_ == 0 {
                            v___x_3391_ = lean_box(0);
                            v___x_3392_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3392_, 0, v_a_3322_);
                            lean_ctor_set(v___x_3392_, 1, v___x_3391_);
                            return v___x_3392_;
                        } else {
                            if v___x_3363_ == 0 {
                                v___x_3393_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
                                v___x_3394_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3394_, 0, v_a_3322_);
                                lean_ctor_set(v___x_3394_, 1, v___x_3393_);
                                return v___x_3394_;
                            } else {
                                v___x_3395_ = lean_unsigned_to_nat(1);
                                v___x_3396_ = lean_nat_add(v_idx_3356_, v___x_3395_);
                                v___x_3397_ = lean_nat_dec_lt(v___x_3396_, v___x_3357_);
                                if v___x_3397_ == 0 {
                                    lean_dec(v___x_3396_);
                                    v___x_3398_ = lean_box(0);
                                    v___x_3399_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_3399_, 0, v_a_3322_);
                                    lean_ctor_set(v___x_3399_, 1, v___x_3398_);
                                    return v___x_3399_;
                                } else {
                                    v_c_3400_ = lean_byte_array_fget(v_array_3355_, v___x_3396_);
                                    v___x_3401_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                                    v___x_3402_ = lean_uint8_dec_le(v___x_3401_, v_c_3400_);
                                    if v___x_3402_ == 0 {
                                        lean_dec(v___x_3396_);
                                        state = 5;
                                        continue;
                                    } else {
                                        v___x_3403_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                        v___x_3404_ = lean_uint8_dec_le(v_c_3400_, v___x_3403_);
                                        if v___x_3404_ == 0 {
                                            lean_dec(v___x_3396_);
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_3405_ = lean_nat_add(v___x_3396_, v___x_3395_);
                                            lean_dec(v___x_3396_);
                                            lean_inc_ref(v_array_3355_);
                                            v_it_x27_3406_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_it_x27_3406_, 0, v_array_3355_);
                                            lean_ctor_set(v_it_x27_3406_, 1, v___x_3405_);
                                            v___x_3407_ = lean_uint8_to_uint32(v_c_3400_);
                                            v___x_3408_ = lean_uint32_to_uint8(v___x_3407_);
                                            v___x_3409_ = lean_uint8_sub(v___x_3408_, v___x_3401_);
                                            v___x_3410_ = lean_uint8_to_nat(v___x_3409_);
                                            v___x_3411_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3406_, v___x_3410_);
                                            v_fst_3412_ = lean_ctor_get(v___x_3411_, 0);
                                            v_snd_3413_ = lean_ctor_get(v___x_3411_, 1);
                                            v_isSharedCheck_3425_ =
                                                (!lean_is_exclusive(v___x_3411_)) as u8;
                                            if v_isSharedCheck_3425_ == 0 {
                                                v___x_3415_ = v___x_3411_;
                                                v_isShared_3416_ = v_isSharedCheck_3425_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_inc(v_snd_3413_);
                                                lean_inc(v_fst_3412_);
                                                lean_dec(v___x_3411_);
                                                v___x_3415_ = lean_box(0);
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
                v_array_3326_ = lean_ctor_get(v_pos_3324_, 0);
                v_idx_3327_ = lean_ctor_get(v_pos_3324_, 1);
                v___x_3328_ = lean_byte_array_size(v_array_3326_);
                v___x_3329_ = lean_nat_dec_lt(v_idx_3327_, v___x_3328_);
                if v___x_3329_ == 0 {
                    lean_dec(v_res_3325_);
                    v___x_3330_ = lean_box(0);
                    v___x_3331_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3331_, 0, v_pos_3324_);
                    lean_ctor_set(v___x_3331_, 1, v___x_3330_);
                    return v___x_3331_;
                } else {
                    v___x_3332_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3333_ = lean_byte_array_fget(v_array_3326_, v_idx_3327_);
                    v___x_3334_ = lean_uint8_dec_eq(v_got_3333_, v___x_3332_);
                    if v___x_3334_ == 0 {
                        lean_dec(v_res_3325_);
                        v___x_3335_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        v___x_3336_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3336_, 0, v_pos_3324_);
                        lean_ctor_set(v___x_3336_, 1, v___x_3335_);
                        return v___x_3336_;
                    } else {
                        lean_inc(v_idx_3327_);
                        lean_inc_ref(v_array_3326_);
                        v_isSharedCheck_3346_ = (!lean_is_exclusive(v_pos_3324_)) as u8;
                        if v_isSharedCheck_3346_ == 0 {
                            v_unused_3347_ = lean_ctor_get(v_pos_3324_, 1);
                            lean_dec(v_unused_3347_);
                            v_unused_3348_ = lean_ctor_get(v_pos_3324_, 0);
                            lean_dec(v_unused_3348_);
                            v___x_3338_ = v_pos_3324_;
                            v_isShared_3339_ = v_isSharedCheck_3346_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_pos_3324_);
                            v___x_3338_ = lean_box(0);
                            v_isShared_3339_ = v_isSharedCheck_3346_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3340_ = lean_unsigned_to_nat(1);
                v___x_3341_ = lean_nat_add(v_idx_3327_, v___x_3340_);
                lean_dec(v_idx_3327_);
                if v_isShared_3339_ == 0 {
                    lean_ctor_set(v___x_3338_, 1, v___x_3341_);
                    v___x_3343_ = v___x_3338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_array_3326_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3341_);
                    v___x_3343_ = v_reuseFailAlloc_3345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3344_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3344_, 0, v___x_3343_);
                lean_ctor_set(v___x_3344_, 1, v_res_3325_);
                return v___x_3344_;
            }
            4 => {
                v___x_3350_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3351_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3351_, 0, v_a_3322_);
                lean_ctor_set(v___x_3351_, 1, v___x_3350_);
                return v___x_3351_;
            }
            5 => {
                v___x_3353_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                v___x_3354_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3354_, 0, v_a_3322_);
                lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                return v___x_3354_;
            }
            6 => {
                v___x_3383_ = lean_unsigned_to_nat(0);
                v___x_3384_ = lean_nat_dec_eq(v_fst_3378_, v___x_3383_);
                if v___x_3384_ == 0 {
                    lean_del_object(v___x_3381_);
                    lean_dec_ref(v_a_3322_);
                    v___x_3385_ = lean_nat_to_int(v_fst_3378_);
                    v_pos_3324_ = v_snd_3379_;
                    v_res_3325_ = v___x_3385_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_snd_3379_);
                    lean_dec(v_fst_3378_);
                    v___x_3386_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3382_ == 0 {
                        lean_ctor_set_tag(v___x_3381_, 1);
                        lean_ctor_set(v___x_3381_, 1, v___x_3386_);
                        lean_ctor_set(v___x_3381_, 0, v_a_3322_);
                        v___x_3388_ = v___x_3381_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3322_);
                        lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3386_);
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
                v___x_3417_ = lean_unsigned_to_nat(0);
                v___x_3418_ = lean_nat_dec_eq(v_fst_3412_, v___x_3417_);
                if v___x_3418_ == 0 {
                    lean_del_object(v___x_3415_);
                    lean_dec_ref(v_a_3322_);
                    v___x_3419_ = lean_nat_to_int(v_fst_3412_);
                    v___x_3420_ = lean_int_neg(v___x_3419_);
                    lean_dec(v___x_3419_);
                    v_pos_3324_ = v_snd_3413_;
                    v_res_3325_ = v___x_3420_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_snd_3413_);
                    lean_dec(v_fst_3412_);
                    v___x_3421_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3416_ == 0 {
                        lean_ctor_set_tag(v___x_3415_, 1);
                        lean_ctor_set(v___x_3415_, 1, v___x_3421_);
                        lean_ctor_set(v___x_3415_, 0, v_a_3322_);
                        v___x_3423_ = v___x_3415_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3322_);
                        lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3421_);
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
    mut v_a_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ = lean_nat_to_int(v_a_3426_);
    return v___x_3427_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(
    mut v_acc_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: u8 = 0;
    let mut v_got_3452_: u8 = 0;
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: u32 = 0;
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3499_: u8 = 0;
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u32 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3430_ = lean_ctor_get(v_a_3429_, 0);
                v_idx_3431_ = lean_ctor_get(v_a_3429_, 1);
                lean_inc(v_idx_3431_);
                v___x_3468_ = lean_byte_array_size(v_array_3430_);
                v___x_3469_ = lean_nat_dec_lt(v_idx_3431_, v___x_3468_);
                if v___x_3469_ == 0 {
                    v___x_3470_ = lean_box(0);
                    lean_inc(v_idx_3431_);
                    v_pos_3433_ = v_a_3429_;
                    v_idx_3434_ = v_idx_3431_;
                    v_err_3435_ = v___x_3470_;
                    state = 1;
                    continue;
                } else {
                    v___x_3471_ = lean_byte_array_fget(v_array_3430_, v_idx_3431_);
                    v___x_3472_ = lean_uint8_once(
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
                            v___x_3474_ = lean_box(0);
                            lean_inc(v_idx_3431_);
                            v_pos_3433_ = v_a_3429_;
                            v_idx_3434_ = v_idx_3431_;
                            v_err_3435_ = v___x_3474_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3475_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                            v___x_3476_ = lean_uint8_dec_le(v___x_3475_, v___x_3471_);
                            if v___x_3476_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                v___x_3477_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                v___x_3478_ = lean_uint8_dec_le(v___x_3471_, v___x_3477_);
                                if v___x_3478_ == 0 {
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3479_ = lean_unsigned_to_nat(1);
                                    v___x_3480_ = lean_nat_add(v_idx_3431_, v___x_3479_);
                                    lean_inc_ref(v_array_3430_);
                                    v_it_x27_3481_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_it_x27_3481_, 0, v_array_3430_);
                                    lean_ctor_set(v_it_x27_3481_, 1, v___x_3480_);
                                    v___x_3482_ = lean_uint8_to_uint32(v___x_3471_);
                                    v___x_3483_ = lean_uint32_to_uint8(v___x_3482_);
                                    v___x_3484_ = lean_uint8_sub(v___x_3483_, v___x_3475_);
                                    v___x_3485_ = lean_uint8_to_nat(v___x_3484_);
                                    v___x_3486_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3481_, v___x_3485_);
                                    v_fst_3487_ = lean_ctor_get(v___x_3486_, 0);
                                    lean_inc(v_fst_3487_);
                                    v_snd_3488_ = lean_ctor_get(v___x_3486_, 1);
                                    lean_inc(v_snd_3488_);
                                    lean_dec_ref(v___x_3486_);
                                    v___x_3489_ = lean_unsigned_to_nat(0);
                                    v___x_3490_ = lean_nat_dec_eq(v_fst_3487_, v___x_3489_);
                                    if v___x_3490_ == 0 {
                                        lean_dec_ref(v_a_3429_);
                                        v___x_3491_ = lean_nat_to_int(v_fst_3487_);
                                        v_pos_3444_ = v_snd_3488_;
                                        v_res_3445_ = v___x_3491_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v_snd_3488_);
                                        lean_dec(v_fst_3487_);
                                        v___x_3492_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                                        lean_inc(v_idx_3431_);
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
                            v___x_3493_ = lean_box(0);
                            lean_inc(v_idx_3431_);
                            v_pos_3433_ = v_a_3429_;
                            v_idx_3434_ = v_idx_3431_;
                            v_err_3435_ = v___x_3493_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_3473_ == 0 {
                                v___x_3494_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
                                lean_inc(v_idx_3431_);
                                v_pos_3433_ = v_a_3429_;
                                v_idx_3434_ = v_idx_3431_;
                                v_err_3435_ = v___x_3494_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3495_ = lean_unsigned_to_nat(1);
                                v___x_3496_ = lean_nat_add(v_idx_3431_, v___x_3495_);
                                v___x_3497_ = lean_nat_dec_lt(v___x_3496_, v___x_3468_);
                                if v___x_3497_ == 0 {
                                    lean_dec(v___x_3496_);
                                    v___x_3498_ = lean_box(0);
                                    lean_inc(v_idx_3431_);
                                    v_pos_3433_ = v_a_3429_;
                                    v_idx_3434_ = v_idx_3431_;
                                    v_err_3435_ = v___x_3498_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_c_3499_ = lean_byte_array_fget(v_array_3430_, v___x_3496_);
                                    v___x_3500_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
                                    v___x_3501_ = lean_uint8_dec_le(v___x_3500_, v_c_3499_);
                                    if v___x_3501_ == 0 {
                                        lean_dec(v___x_3496_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3502_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
                                        v___x_3503_ = lean_uint8_dec_le(v_c_3499_, v___x_3502_);
                                        if v___x_3503_ == 0 {
                                            lean_dec(v___x_3496_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_3504_ = lean_nat_add(v___x_3496_, v___x_3495_);
                                            lean_dec(v___x_3496_);
                                            lean_inc_ref(v_array_3430_);
                                            v_it_x27_3505_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_it_x27_3505_, 0, v_array_3430_);
                                            lean_ctor_set(v_it_x27_3505_, 1, v___x_3504_);
                                            v___x_3506_ = lean_uint8_to_uint32(v_c_3499_);
                                            v___x_3507_ = lean_uint32_to_uint8(v___x_3506_);
                                            v___x_3508_ = lean_uint8_sub(v___x_3507_, v___x_3500_);
                                            v___x_3509_ = lean_uint8_to_nat(v___x_3508_);
                                            v___x_3510_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3505_, v___x_3509_);
                                            v_fst_3511_ = lean_ctor_get(v___x_3510_, 0);
                                            lean_inc(v_fst_3511_);
                                            v_snd_3512_ = lean_ctor_get(v___x_3510_, 1);
                                            lean_inc(v_snd_3512_);
                                            lean_dec_ref(v___x_3510_);
                                            v___x_3513_ = lean_unsigned_to_nat(0);
                                            v___x_3514_ = lean_nat_dec_eq(v_fst_3511_, v___x_3513_);
                                            if v___x_3514_ == 0 {
                                                lean_dec_ref(v_a_3429_);
                                                v___x_3515_ = lean_nat_to_int(v_fst_3511_);
                                                v___x_3516_ = lean_int_neg(v___x_3515_);
                                                lean_dec(v___x_3515_);
                                                v_pos_3444_ = v_snd_3512_;
                                                v_res_3445_ = v___x_3516_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_dec(v_snd_3512_);
                                                lean_dec(v_fst_3511_);
                                                v___x_3517_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                                                lean_inc(v_idx_3431_);
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
                lean_dec(v_idx_3434_);
                lean_dec(v_idx_3431_);
                if v___x_3436_ == 0 {
                    lean_dec_ref(v_acc_3428_);
                    lean_inc(v_err_3435_);
                    v___x_3437_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3437_, 0, v_pos_3433_);
                    lean_ctor_set(v___x_3437_, 1, v_err_3435_);
                    return v___x_3437_;
                } else {
                    v___x_3438_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3438_, 0, v_pos_3433_);
                    lean_ctor_set(v___x_3438_, 1, v_acc_3428_);
                    return v___x_3438_;
                }
            }
            2 => {
                v___x_3440_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                lean_inc(v_idx_3431_);
                v_pos_3433_ = v_a_3429_;
                v_idx_3434_ = v_idx_3431_;
                v_err_3435_ = v___x_3440_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3442_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
                lean_inc(v_idx_3431_);
                v_pos_3433_ = v_a_3429_;
                v_idx_3434_ = v_idx_3431_;
                v_err_3435_ = v___x_3442_;
                state = 1;
                continue;
            }
            4 => {
                v_array_3446_ = lean_ctor_get(v_pos_3444_, 0);
                v_idx_3447_ = lean_ctor_get(v_pos_3444_, 1);
                lean_inc(v_idx_3447_);
                v___x_3448_ = lean_byte_array_size(v_array_3446_);
                v___x_3449_ = lean_nat_dec_lt(v_idx_3447_, v___x_3448_);
                if v___x_3449_ == 0 {
                    lean_dec(v_res_3445_);
                    v___x_3450_ = lean_box(0);
                    v_pos_3433_ = v_pos_3444_;
                    v_idx_3434_ = v_idx_3447_;
                    v_err_3435_ = v___x_3450_;
                    state = 1;
                    continue;
                } else {
                    v___x_3451_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3452_ = lean_byte_array_fget(v_array_3446_, v_idx_3447_);
                    v___x_3453_ = lean_uint8_dec_eq(v_got_3452_, v___x_3451_);
                    if v___x_3453_ == 0 {
                        lean_dec(v_res_3445_);
                        v___x_3454_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        v_pos_3433_ = v_pos_3444_;
                        v_idx_3434_ = v_idx_3447_;
                        v_err_3435_ = v___x_3454_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_array_3446_);
                        lean_dec(v_idx_3431_);
                        v_isSharedCheck_3465_ = (!lean_is_exclusive(v_pos_3444_)) as u8;
                        if v_isSharedCheck_3465_ == 0 {
                            v_unused_3466_ = lean_ctor_get(v_pos_3444_, 1);
                            lean_dec(v_unused_3466_);
                            v_unused_3467_ = lean_ctor_get(v_pos_3444_, 0);
                            lean_dec(v_unused_3467_);
                            v___x_3456_ = v_pos_3444_;
                            v_isShared_3457_ = v_isSharedCheck_3465_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_pos_3444_);
                            v___x_3456_ = lean_box(0);
                            v_isShared_3457_ = v_isSharedCheck_3465_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_3458_ = lean_unsigned_to_nat(1);
                v___x_3459_ = lean_nat_add(v_idx_3447_, v___x_3458_);
                lean_dec(v_idx_3447_);
                if v_isShared_3457_ == 0 {
                    lean_ctor_set(v___x_3456_, 1, v___x_3459_);
                    v___x_3461_ = v___x_3456_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_array_3446_);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3459_);
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
    mut v_a_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v_array_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v_got_3537_: u8 = 0;
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3554_: u8 = 0;
    let mut v_unused_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3521_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0;
                v___x_3522_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_3521_, v_a_3520_);
                if lean_obj_tag(v___x_3522_) == 0 {
                    v_pos_3523_ = lean_ctor_get(v___x_3522_, 0);
                    v_res_3524_ = lean_ctor_get(v___x_3522_, 1);
                    v_isSharedCheck_3557_ = (!lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3557_ == 0 {
                        v___x_3526_ = v___x_3522_;
                        v_isShared_3527_ = v_isSharedCheck_3557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3524_);
                        lean_inc(v_pos_3523_);
                        lean_dec(v___x_3522_);
                        v___x_3526_ = lean_box(0);
                        v_isShared_3527_ = v_isSharedCheck_3557_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3522_;
                }
            }
            1 => {
                v_array_3528_ = lean_ctor_get(v_pos_3523_, 0);
                v_idx_3529_ = lean_ctor_get(v_pos_3523_, 1);
                v___x_3530_ = lean_byte_array_size(v_array_3528_);
                v___x_3531_ = lean_nat_dec_lt(v_idx_3529_, v___x_3530_);
                if v___x_3531_ == 0 {
                    lean_dec(v_res_3524_);
                    v___x_3532_ = lean_box(0);
                    if v_isShared_3527_ == 0 {
                        lean_ctor_set_tag(v___x_3526_, 1);
                        lean_ctor_set(v___x_3526_, 1, v___x_3532_);
                        v___x_3534_ = v___x_3526_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_pos_3523_);
                        lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3532_);
                        v___x_3534_ = v_reuseFailAlloc_3535_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3536_ = lean_uint8_once(
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
                        lean_dec(v_res_3524_);
                        v___x_3539_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        if v_isShared_3527_ == 0 {
                            lean_ctor_set_tag(v___x_3526_, 1);
                            lean_ctor_set(v___x_3526_, 1, v___x_3539_);
                            v___x_3541_ = v___x_3526_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_pos_3523_);
                            lean_ctor_set(v_reuseFailAlloc_3542_, 1, v___x_3539_);
                            v___x_3541_ = v_reuseFailAlloc_3542_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_3529_);
                        lean_inc_ref(v_array_3528_);
                        v_isSharedCheck_3554_ = (!lean_is_exclusive(v_pos_3523_)) as u8;
                        if v_isSharedCheck_3554_ == 0 {
                            v_unused_3555_ = lean_ctor_get(v_pos_3523_, 1);
                            lean_dec(v_unused_3555_);
                            v_unused_3556_ = lean_ctor_get(v_pos_3523_, 0);
                            lean_dec(v_unused_3556_);
                            v___x_3544_ = v_pos_3523_;
                            v_isShared_3545_ = v_isSharedCheck_3554_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_pos_3523_);
                            v___x_3544_ = lean_box(0);
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
                v___x_3546_ = lean_unsigned_to_nat(1);
                v___x_3547_ = lean_nat_add(v_idx_3529_, v___x_3546_);
                lean_dec(v_idx_3529_);
                if v_isShared_3545_ == 0 {
                    lean_ctor_set(v___x_3544_, 1, v___x_3547_);
                    v___x_3549_ = v___x_3544_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_array_3528_);
                    lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___x_3547_);
                    v___x_3549_ = v_reuseFailAlloc_3553_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3527_ == 0 {
                    lean_ctor_set(v___x_3526_, 0, v___x_3549_);
                    v___x_3551_ = v___x_3526_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
                    lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_res_3524_);
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
    mut v_a_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v_got_3566_: u8 = 0;
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3583_: u8 = 0;
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u32 = 0;
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v_array_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: u8 = 0;
    let mut v_got_3609_: u8 = 0;
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_pos_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_unused_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v_reuseFailAlloc_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut v_unused_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3559_ = lean_ctor_get(v_a_3558_, 0);
                v_idx_3560_ = lean_ctor_get(v_a_3558_, 1);
                v___x_3561_ = lean_byte_array_size(v_array_3559_);
                v___x_3562_ = lean_nat_dec_lt(v_idx_3560_, v___x_3561_);
                if v___x_3562_ == 0 {
                    v___x_3563_ = lean_box(0);
                    v___x_3564_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3564_, 0, v_a_3558_);
                    lean_ctor_set(v___x_3564_, 1, v___x_3563_);
                    return v___x_3564_;
                } else {
                    v___x_3565_ = lean_uint8_once(
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
                        v___x_3568_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5,
                        );
                        v___x_3569_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3569_, 0, v_a_3558_);
                        lean_ctor_set(v___x_3569_, 1, v___x_3568_);
                        return v___x_3569_;
                    } else {
                        lean_inc(v_idx_3560_);
                        lean_inc_ref(v_array_3559_);
                        v_isSharedCheck_3652_ = (!lean_is_exclusive(v_a_3558_)) as u8;
                        if v_isSharedCheck_3652_ == 0 {
                            v_unused_3653_ = lean_ctor_get(v_a_3558_, 1);
                            lean_dec(v_unused_3653_);
                            v_unused_3654_ = lean_ctor_get(v_a_3558_, 0);
                            lean_dec(v_unused_3654_);
                            v___x_3571_ = v_a_3558_;
                            v_isShared_3572_ = v_isSharedCheck_3652_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3558_);
                            v___x_3571_ = lean_box(0);
                            v_isShared_3572_ = v_isSharedCheck_3652_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3573_ = lean_unsigned_to_nat(1);
                v___x_3574_ = lean_nat_add(v_idx_3560_, v___x_3573_);
                lean_dec(v_idx_3560_);
                lean_inc(v___x_3574_);
                lean_inc_ref(v_array_3559_);
                if v_isShared_3572_ == 0 {
                    lean_ctor_set(v___x_3571_, 1, v___x_3574_);
                    v___x_3576_ = v___x_3571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_array_3559_);
                    lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3580_ = lean_nat_dec_lt(v___x_3574_, v___x_3561_);
                if v___x_3580_ == 0 {
                    lean_dec(v___x_3574_);
                    lean_dec_ref(v_array_3559_);
                    v___x_3581_ = lean_box(0);
                    v___x_3582_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3582_, 0, v___x_3576_);
                    lean_ctor_set(v___x_3582_, 1, v___x_3581_);
                    return v___x_3582_;
                } else {
                    v_c_3583_ = lean_byte_array_fget(v_array_3559_, v___x_3574_);
                    v___x_3584_ = lean_uint8_once(
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
                        lean_dec(v___x_3574_);
                        lean_dec_ref(v_array_3559_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3586_ = lean_uint8_once(
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
                            lean_dec(v___x_3574_);
                            lean_dec_ref(v_array_3559_);
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v___x_3576_);
                            v___x_3588_ = lean_nat_add(v___x_3574_, v___x_3573_);
                            lean_dec(v___x_3574_);
                            v_it_x27_3589_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_it_x27_3589_, 0, v_array_3559_);
                            lean_ctor_set(v_it_x27_3589_, 1, v___x_3588_);
                            v___x_3590_ = lean_uint8_to_uint32(v_c_3583_);
                            v___x_3591_ = lean_uint32_to_uint8(v___x_3590_);
                            v___x_3592_ = lean_uint8_sub(v___x_3591_, v___x_3584_);
                            v___x_3593_ = lean_uint8_to_nat(v___x_3592_);
                            v___x_3594_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_3589_, v___x_3593_);
                            v_fst_3595_ = lean_ctor_get(v___x_3594_, 0);
                            v_snd_3596_ = lean_ctor_get(v___x_3594_, 1);
                            v_isSharedCheck_3650_ = (!lean_is_exclusive(v___x_3594_)) as u8;
                            if v_isSharedCheck_3650_ == 0 {
                                v___x_3598_ = v___x_3594_;
                                v_isShared_3599_ = v_isSharedCheck_3650_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_snd_3596_);
                                lean_inc(v_fst_3595_);
                                lean_dec(v___x_3594_);
                                v___x_3598_ = lean_box(0);
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
                v___x_3579_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3579_, 0, v___x_3576_);
                lean_ctor_set(v___x_3579_, 1, v___x_3578_);
                return v___x_3579_;
            }
            4 => {
                v___x_3600_ = lean_unsigned_to_nat(0);
                v___x_3601_ = lean_nat_dec_eq(v_fst_3595_, v___x_3600_);
                if v___x_3601_ == 0 {
                    v_array_3602_ = lean_ctor_get(v_snd_3596_, 0);
                    v_idx_3603_ = lean_ctor_get(v_snd_3596_, 1);
                    v___x_3604_ = lean_byte_array_size(v_array_3602_);
                    v___x_3605_ = lean_nat_dec_lt(v_idx_3603_, v___x_3604_);
                    if v___x_3605_ == 0 {
                        lean_del_object(v___x_3598_);
                        lean_dec(v_fst_3595_);
                        v___x_3606_ = lean_box(0);
                        v___x_3607_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_3607_, 0, v_snd_3596_);
                        lean_ctor_set(v___x_3607_, 1, v___x_3606_);
                        return v___x_3607_;
                    } else {
                        v___x_3608_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                        v_got_3609_ = lean_byte_array_fget(v_array_3602_, v_idx_3603_);
                        v___x_3610_ = lean_uint8_dec_eq(v_got_3609_, v___x_3608_);
                        if v___x_3610_ == 0 {
                            lean_del_object(v___x_3598_);
                            lean_dec(v_fst_3595_);
                            v___x_3611_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                            v___x_3612_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3612_, 0, v_snd_3596_);
                            lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                            return v___x_3612_;
                        } else {
                            lean_inc(v_idx_3603_);
                            lean_inc_ref(v_array_3602_);
                            v_isSharedCheck_3645_ = (!lean_is_exclusive(v_snd_3596_)) as u8;
                            if v_isSharedCheck_3645_ == 0 {
                                v_unused_3646_ = lean_ctor_get(v_snd_3596_, 1);
                                lean_dec(v_unused_3646_);
                                v_unused_3647_ = lean_ctor_get(v_snd_3596_, 0);
                                lean_dec(v_unused_3647_);
                                v___x_3614_ = v_snd_3596_;
                                v_isShared_3615_ = v_isSharedCheck_3645_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v_snd_3596_);
                                v___x_3614_ = lean_box(0);
                                v_isShared_3615_ = v_isSharedCheck_3645_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_3598_);
                    lean_dec(v_fst_3595_);
                    v___x_3648_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    v___x_3649_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3649_, 0, v_snd_3596_);
                    lean_ctor_set(v___x_3649_, 1, v___x_3648_);
                    return v___x_3649_;
                }
            }
            5 => {
                v___x_3616_ = lean_nat_add(v_idx_3603_, v___x_3573_);
                lean_dec(v_idx_3603_);
                if v_isShared_3615_ == 0 {
                    lean_ctor_set(v___x_3614_, 1, v___x_3616_);
                    v___x_3618_ = v___x_3614_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_array_3602_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3644_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3619_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_3618_);
                if lean_obj_tag(v___x_3619_) == 0 {
                    v_pos_3620_ = lean_ctor_get(v___x_3619_, 0);
                    v_res_3621_ = lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3634_ = (!lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3634_ == 0 {
                        v___x_3623_ = v___x_3619_;
                        v_isShared_3624_ = v_isSharedCheck_3634_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_res_3621_);
                        lean_inc(v_pos_3620_);
                        lean_dec(v___x_3619_);
                        v___x_3623_ = lean_box(0);
                        v_isShared_3624_ = v_isSharedCheck_3634_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3598_);
                    lean_dec(v_fst_3595_);
                    v_pos_3635_ = lean_ctor_get(v___x_3619_, 0);
                    v_err_3636_ = lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3643_ = (!lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3643_ == 0 {
                        v___x_3638_ = v___x_3619_;
                        v_isShared_3639_ = v_isSharedCheck_3643_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_err_3636_);
                        lean_inc(v_pos_3635_);
                        lean_dec(v___x_3619_);
                        v___x_3638_ = lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3643_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3625_ = lean_nat_to_int(v_fst_3595_);
                v___x_3626_ = lean_int_neg(v___x_3625_);
                lean_dec(v___x_3625_);
                v___x_3627_ = lean_nat_abs(v___x_3626_);
                lean_dec(v___x_3626_);
                if v_isShared_3599_ == 0 {
                    lean_ctor_set(v___x_3598_, 1, v_res_3621_);
                    lean_ctor_set(v___x_3598_, 0, v___x_3627_);
                    v___x_3629_ = v___x_3598_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3627_);
                    lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_res_3621_);
                    v___x_3629_ = v_reuseFailAlloc_3633_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3624_ == 0 {
                    lean_ctor_set(v___x_3623_, 1, v___x_3629_);
                    v___x_3631_ = v___x_3623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_pos_3620_);
                    lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___x_3629_);
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
                    v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_pos_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_err_3636_);
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
    mut v_acc_3655_: *mut LeanObject,
    mut v_a_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v_idx_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: u8 = 0;
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_unused_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_3656_);
                v___x_3674_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_3656_);
                if lean_obj_tag(v___x_3674_) == 0 {
                    if lean_obj_tag(v___x_3674_) == 0 {
                        lean_dec_ref(v_a_3656_);
                        v_pos_3675_ = lean_ctor_get(v___x_3674_, 0);
                        lean_inc(v_pos_3675_);
                        v_res_3676_ = lean_ctor_get(v___x_3674_, 1);
                        lean_inc(v_res_3676_);
                        lean_dec_ref_known(v___x_3674_, 2);
                        v___x_3677_ = lean_array_push(v_acc_3655_, v_res_3676_);
                        v_acc_3655_ = v___x_3677_;
                        v_a_3656_ = v_pos_3675_;
                        state = 0;
                        continue;
                    } else {
                        v_pos_3679_ = lean_ctor_get(v___x_3674_, 0);
                        lean_inc(v_pos_3679_);
                        v_err_3680_ = lean_ctor_get(v___x_3674_, 1);
                        lean_inc(v_err_3680_);
                        lean_dec_ref_known(v___x_3674_, 2);
                        v_pos_3658_ = v_pos_3679_;
                        v_err_3659_ = v_err_3680_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_err_3681_ = lean_ctor_get(v___x_3674_, 1);
                    lean_inc(v_err_3681_);
                    lean_dec_ref_known(v___x_3674_, 2);
                    lean_inc_ref(v_a_3656_);
                    v_pos_3658_ = v_a_3656_;
                    v_err_3659_ = v_err_3681_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_idx_3660_ = lean_ctor_get(v_a_3656_, 1);
                v_isSharedCheck_3672_ = (!lean_is_exclusive(v_a_3656_)) as u8;
                if v_isSharedCheck_3672_ == 0 {
                    v_unused_3673_ = lean_ctor_get(v_a_3656_, 0);
                    lean_dec(v_unused_3673_);
                    v___x_3662_ = v_a_3656_;
                    v_isShared_3663_ = v_isSharedCheck_3672_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_idx_3660_);
                    lean_dec(v_a_3656_);
                    v___x_3662_ = lean_box(0);
                    v_isShared_3663_ = v_isSharedCheck_3672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_idx_3664_ = lean_ctor_get(v_pos_3658_, 1);
                v___x_3665_ = lean_nat_dec_eq(v_idx_3660_, v_idx_3664_);
                lean_dec(v_idx_3660_);
                if v___x_3665_ == 0 {
                    lean_dec_ref(v_acc_3655_);
                    if v_isShared_3663_ == 0 {
                        lean_ctor_set_tag(v___x_3662_, 1);
                        lean_ctor_set(v___x_3662_, 1, v_err_3659_);
                        lean_ctor_set(v___x_3662_, 0, v_pos_3658_);
                        v___x_3667_ = v___x_3662_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_pos_3658_);
                        lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_err_3659_);
                        v___x_3667_ = v_reuseFailAlloc_3668_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_err_3659_);
                    if v_isShared_3663_ == 0 {
                        lean_ctor_set(v___x_3662_, 1, v_acc_3655_);
                        lean_ctor_set(v___x_3662_, 0, v_pos_3658_);
                        v___x_3670_ = v___x_3662_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_pos_3658_);
                        lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_acc_3655_);
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
    mut v_ident_3687_: *mut LeanObject,
    mut v_a_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v_array_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: u8 = 0;
    let mut v_got_3704_: u8 = 0;
    let mut v___x_3705_: u8 = 0;
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v_array_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v_got_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3773_: u8 = 0;
    let mut v_unused_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_pos_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_pos_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3790_: u8 = 0;
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut v_reuseFailAlloc_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v_unused_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v_pos_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_3688_);
                if lean_obj_tag(v___x_3689_) == 0 {
                    v_pos_3690_ = lean_ctor_get(v___x_3689_, 0);
                    v_res_3691_ = lean_ctor_get(v___x_3689_, 1);
                    v_isSharedCheck_3799_ = (!lean_is_exclusive(v___x_3689_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3693_ = v___x_3689_;
                        v_isShared_3694_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3691_);
                        lean_inc(v_pos_3690_);
                        lean_dec(v___x_3689_);
                        v___x_3693_ = lean_box(0);
                        v_isShared_3694_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_ident_3687_);
                    v_pos_3800_ = lean_ctor_get(v___x_3689_, 0);
                    v_err_3801_ = lean_ctor_get(v___x_3689_, 1);
                    v_isSharedCheck_3808_ = (!lean_is_exclusive(v___x_3689_)) as u8;
                    if v_isSharedCheck_3808_ == 0 {
                        v___x_3803_ = v___x_3689_;
                        v_isShared_3804_ = v_isSharedCheck_3808_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_err_3801_);
                        lean_inc(v_pos_3800_);
                        lean_dec(v___x_3689_);
                        v___x_3803_ = lean_box(0);
                        v_isShared_3804_ = v_isSharedCheck_3808_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_array_3695_ = lean_ctor_get(v_pos_3690_, 0);
                v_idx_3696_ = lean_ctor_get(v_pos_3690_, 1);
                v___x_3697_ = lean_byte_array_size(v_array_3695_);
                v___x_3698_ = lean_nat_dec_lt(v_idx_3696_, v___x_3697_);
                if v___x_3698_ == 0 {
                    lean_dec(v_res_3691_);
                    lean_dec(v_ident_3687_);
                    v___x_3699_ = lean_box(0);
                    if v_isShared_3694_ == 0 {
                        lean_ctor_set_tag(v___x_3693_, 1);
                        lean_ctor_set(v___x_3693_, 1, v___x_3699_);
                        v___x_3701_ = v___x_3693_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_pos_3690_);
                        lean_ctor_set(v_reuseFailAlloc_3702_, 1, v___x_3699_);
                        v___x_3701_ = v_reuseFailAlloc_3702_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3703_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                    v_got_3704_ = lean_byte_array_fget(v_array_3695_, v_idx_3696_);
                    v___x_3705_ = lean_uint8_dec_eq(v_got_3704_, v___x_3703_);
                    if v___x_3705_ == 0 {
                        lean_dec(v_res_3691_);
                        lean_dec(v_ident_3687_);
                        v___x_3706_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                        if v_isShared_3694_ == 0 {
                            lean_ctor_set_tag(v___x_3693_, 1);
                            lean_ctor_set(v___x_3693_, 1, v___x_3706_);
                            v___x_3708_ = v___x_3693_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_pos_3690_);
                            lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3706_);
                            v___x_3708_ = v_reuseFailAlloc_3709_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_3696_);
                        lean_inc_ref(v_array_3695_);
                        lean_del_object(v___x_3693_);
                        v_isSharedCheck_3796_ = (!lean_is_exclusive(v_pos_3690_)) as u8;
                        if v_isSharedCheck_3796_ == 0 {
                            v_unused_3797_ = lean_ctor_get(v_pos_3690_, 1);
                            lean_dec(v_unused_3797_);
                            v_unused_3798_ = lean_ctor_get(v_pos_3690_, 0);
                            lean_dec(v_unused_3798_);
                            v___x_3711_ = v_pos_3690_;
                            v_isShared_3712_ = v_isSharedCheck_3796_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_pos_3690_);
                            v___x_3711_ = lean_box(0);
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
                v___x_3713_ = lean_unsigned_to_nat(1);
                v___x_3714_ = lean_nat_add(v_idx_3696_, v___x_3713_);
                lean_dec(v_idx_3696_);
                if v_isShared_3712_ == 0 {
                    lean_ctor_set(v___x_3711_, 1, v___x_3714_);
                    v___x_3716_ = v___x_3711_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_array_3695_);
                    lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3714_);
                    v___x_3716_ = v_reuseFailAlloc_3795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3717_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_3716_);
                if lean_obj_tag(v___x_3717_) == 0 {
                    v_pos_3718_ = lean_ctor_get(v___x_3717_, 0);
                    lean_inc(v_pos_3718_);
                    v_res_3719_ = lean_ctor_get(v___x_3717_, 1);
                    lean_inc(v_res_3719_);
                    lean_dec_ref_known(v___x_3717_, 2);
                    v___x_3720_ = lean_unsigned_to_nat(0);
                    v___x_3721_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0;
                    v___x_3722_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_3721_, v_pos_3718_);
                    if lean_obj_tag(v___x_3722_) == 0 {
                        v_pos_3723_ = lean_ctor_get(v___x_3722_, 0);
                        v_res_3724_ = lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3776_ = (!lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3776_ == 0 {
                            v___x_3726_ = v___x_3722_;
                            v_isShared_3727_ = v_isSharedCheck_3776_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_res_3724_);
                            lean_inc(v_pos_3723_);
                            lean_dec(v___x_3722_);
                            v___x_3726_ = lean_box(0);
                            v_isShared_3727_ = v_isSharedCheck_3776_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_3719_);
                        lean_dec(v_res_3691_);
                        lean_dec(v_ident_3687_);
                        v_pos_3777_ = lean_ctor_get(v___x_3722_, 0);
                        v_err_3778_ = lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3785_ = (!lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3785_ == 0 {
                            v___x_3780_ = v___x_3722_;
                            v_isShared_3781_ = v_isSharedCheck_3785_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_err_3778_);
                            lean_inc(v_pos_3777_);
                            lean_dec(v___x_3722_);
                            v___x_3780_ = lean_box(0);
                            v_isShared_3781_ = v_isSharedCheck_3785_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_res_3691_);
                    lean_dec(v_ident_3687_);
                    v_pos_3786_ = lean_ctor_get(v___x_3717_, 0);
                    v_err_3787_ = lean_ctor_get(v___x_3717_, 1);
                    v_isSharedCheck_3794_ = (!lean_is_exclusive(v___x_3717_)) as u8;
                    if v_isSharedCheck_3794_ == 0 {
                        v___x_3789_ = v___x_3717_;
                        v_isShared_3790_ = v_isSharedCheck_3794_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_err_3787_);
                        lean_inc(v_pos_3786_);
                        lean_dec(v___x_3717_);
                        v___x_3789_ = lean_box(0);
                        v_isShared_3790_ = v_isSharedCheck_3794_;
                        state = 17;
                        continue;
                    }
                }
            }
            6 => {
                v_array_3728_ = lean_ctor_get(v_pos_3723_, 0);
                v_idx_3729_ = lean_ctor_get(v_pos_3723_, 1);
                v___x_3730_ = lean_byte_array_size(v_array_3728_);
                v___x_3731_ = lean_nat_dec_lt(v_idx_3729_, v___x_3730_);
                if v___x_3731_ == 0 {
                    lean_dec(v_res_3724_);
                    lean_dec(v_res_3719_);
                    lean_dec(v_res_3691_);
                    lean_dec(v_ident_3687_);
                    v___x_3732_ = lean_box(0);
                    if v_isShared_3727_ == 0 {
                        lean_ctor_set_tag(v___x_3726_, 1);
                        lean_ctor_set(v___x_3726_, 1, v___x_3732_);
                        v___x_3734_ = v___x_3726_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_pos_3723_);
                        lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3732_);
                        v___x_3734_ = v_reuseFailAlloc_3735_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_3736_ = lean_uint8_once(
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
                        lean_dec(v_res_3724_);
                        lean_dec(v_res_3719_);
                        lean_dec(v_res_3691_);
                        lean_dec(v_ident_3687_);
                        v___x_3739_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4,
                        );
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set_tag(v___x_3726_, 1);
                            lean_ctor_set(v___x_3726_, 1, v___x_3739_);
                            v___x_3741_ = v___x_3726_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_pos_3723_);
                            lean_ctor_set(v_reuseFailAlloc_3742_, 1, v___x_3739_);
                            v___x_3741_ = v_reuseFailAlloc_3742_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_3729_);
                        lean_inc_ref(v_array_3728_);
                        v_isSharedCheck_3773_ = (!lean_is_exclusive(v_pos_3723_)) as u8;
                        if v_isSharedCheck_3773_ == 0 {
                            v_unused_3774_ = lean_ctor_get(v_pos_3723_, 1);
                            lean_dec(v_unused_3774_);
                            v_unused_3775_ = lean_ctor_get(v_pos_3723_, 0);
                            lean_dec(v_unused_3775_);
                            v___x_3744_ = v_pos_3723_;
                            v_isShared_3745_ = v_isSharedCheck_3773_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v_pos_3723_);
                            v___x_3744_ = lean_box(0);
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
                lean_dec(v_idx_3729_);
                if v_isShared_3745_ == 0 {
                    lean_ctor_set(v___x_3744_, 1, v___x_3746_);
                    v___x_3748_ = v___x_3744_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_array_3728_);
                    lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3746_);
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
                        v___x_3754_ = lean_alloc_ctor(2, 5, (0) as u32);
                        lean_ctor_set(v___x_3754_, 0, v_ident_3687_);
                        lean_ctor_set(v___x_3754_, 1, v_res_3691_);
                        lean_ctor_set(v___x_3754_, 2, v___x_3753_);
                        lean_ctor_set(v___x_3754_, 3, v_res_3719_);
                        lean_ctor_set(v___x_3754_, 4, v_res_3724_);
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set(v___x_3726_, 1, v___x_3754_);
                            lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3756_ = v___x_3726_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3748_);
                            lean_ctor_set(v_reuseFailAlloc_3757_, 1, v___x_3754_);
                            v___x_3756_ = v_reuseFailAlloc_3757_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_3724_);
                        v___x_3758_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_3758_, 0, v_ident_3687_);
                        lean_ctor_set(v___x_3758_, 1, v_res_3691_);
                        lean_ctor_set(v___x_3758_, 2, v_res_3719_);
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set(v___x_3726_, 1, v___x_3758_);
                            lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3760_ = v___x_3726_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3748_);
                            lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3758_);
                            v___x_3760_ = v_reuseFailAlloc_3761_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_res_3691_);
                    v___x_3762_ = lean_array_get_size(v_res_3724_);
                    lean_dec(v_res_3724_);
                    v___x_3763_ = lean_nat_dec_eq(v___x_3762_, v___x_3720_);
                    if v___x_3763_ == 0 {
                        lean_dec(v_res_3719_);
                        lean_dec(v_ident_3687_);
                        v___x_3764_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2;
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set_tag(v___x_3726_, 1);
                            lean_ctor_set(v___x_3726_, 1, v___x_3764_);
                            lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3766_ = v___x_3726_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3748_);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3764_);
                            v___x_3766_ = v_reuseFailAlloc_3767_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v___x_3768_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3768_, 0, v_ident_3687_);
                        lean_ctor_set(v___x_3768_, 1, v_res_3719_);
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set(v___x_3726_, 1, v___x_3768_);
                            lean_ctor_set(v___x_3726_, 0, v___x_3748_);
                            v___x_3770_ = v___x_3726_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3748_);
                            lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3768_);
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
                    v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_pos_3777_);
                    lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_err_3778_);
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
                    v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_pos_3786_);
                    lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_err_3787_);
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
                    v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_pos_3800_);
                    lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_err_3801_);
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
    mut v_a_3809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3819_: u8 = 0;
    let mut v___x_3820_: u8 = 0;
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: u8 = 0;
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u32 = 0;
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v_array_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v_got_3852_: u8 = 0;
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: u8 = 0;
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut v_unused_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_reuseFailAlloc_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_unused_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3813_ = lean_ctor_get(v_a_3809_, 0);
                v_idx_3814_ = lean_ctor_get(v_a_3809_, 1);
                v___x_3815_ = lean_byte_array_size(v_array_3813_);
                v___x_3816_ = lean_nat_dec_lt(v_idx_3814_, v___x_3815_);
                if v___x_3816_ == 0 {
                    v___x_3817_ = lean_box(0);
                    v___x_3818_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3818_, 0, v_a_3809_);
                    lean_ctor_set(v___x_3818_, 1, v___x_3817_);
                    return v___x_3818_;
                } else {
                    v_c_3819_ = lean_byte_array_fget(v_array_3813_, v_idx_3814_);
                    v___x_3820_ = lean_uint8_once(
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
                        v___x_3822_ = lean_uint8_once(
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
                            lean_inc(v_idx_3814_);
                            lean_inc_ref(v_array_3813_);
                            v_isSharedCheck_3884_ = (!lean_is_exclusive(v_a_3809_)) as u8;
                            if v_isSharedCheck_3884_ == 0 {
                                v_unused_3885_ = lean_ctor_get(v_a_3809_, 1);
                                lean_dec(v_unused_3885_);
                                v_unused_3886_ = lean_ctor_get(v_a_3809_, 0);
                                lean_dec(v_unused_3886_);
                                v___x_3825_ = v_a_3809_;
                                v_isShared_3826_ = v_isSharedCheck_3884_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_3809_);
                                v___x_3825_ = lean_box(0);
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
                v___x_3812_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3812_, 0, v_a_3809_);
                lean_ctor_set(v___x_3812_, 1, v___x_3811_);
                return v___x_3812_;
            }
            2 => {
                v___x_3827_ = lean_unsigned_to_nat(1);
                v___x_3828_ = lean_nat_add(v_idx_3814_, v___x_3827_);
                lean_dec(v_idx_3814_);
                if v_isShared_3826_ == 0 {
                    lean_ctor_set(v___x_3825_, 1, v___x_3828_);
                    v_it_x27_3830_ = v___x_3825_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_array_3813_);
                    lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___x_3828_);
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
                v_fst_3836_ = lean_ctor_get(v___x_3835_, 0);
                v_snd_3837_ = lean_ctor_get(v___x_3835_, 1);
                v_isSharedCheck_3882_ = (!lean_is_exclusive(v___x_3835_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v___x_3839_ = v___x_3835_;
                    v_isShared_3840_ = v_isSharedCheck_3882_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_3837_);
                    lean_inc(v_fst_3836_);
                    lean_dec(v___x_3835_);
                    v___x_3839_ = lean_box(0);
                    v_isShared_3840_ = v_isSharedCheck_3882_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3841_ = lean_unsigned_to_nat(0);
                v___x_3842_ = lean_nat_dec_eq(v_fst_3836_, v___x_3841_);
                if v___x_3842_ == 0 {
                    v_array_3843_ = lean_ctor_get(v_snd_3837_, 0);
                    v_idx_3844_ = lean_ctor_get(v_snd_3837_, 1);
                    v___x_3845_ = lean_byte_array_size(v_array_3843_);
                    v___x_3846_ = lean_nat_dec_lt(v_idx_3844_, v___x_3845_);
                    if v___x_3846_ == 0 {
                        lean_dec(v_fst_3836_);
                        v___x_3847_ = lean_box(0);
                        if v_isShared_3840_ == 0 {
                            lean_ctor_set_tag(v___x_3839_, 1);
                            lean_ctor_set(v___x_3839_, 1, v___x_3847_);
                            lean_ctor_set(v___x_3839_, 0, v_snd_3837_);
                            v___x_3849_ = v___x_3839_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_snd_3837_);
                            lean_ctor_set(v_reuseFailAlloc_3850_, 1, v___x_3847_);
                            v___x_3849_ = v_reuseFailAlloc_3850_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_3851_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
                        v_got_3852_ = lean_byte_array_fget(v_array_3843_, v_idx_3844_);
                        v___x_3853_ = lean_uint8_dec_eq(v_got_3852_, v___x_3851_);
                        if v___x_3853_ == 0 {
                            lean_dec(v_fst_3836_);
                            v___x_3854_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
                            if v_isShared_3840_ == 0 {
                                lean_ctor_set_tag(v___x_3839_, 1);
                                lean_ctor_set(v___x_3839_, 1, v___x_3854_);
                                lean_ctor_set(v___x_3839_, 0, v_snd_3837_);
                                v___x_3856_ = v___x_3839_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_snd_3837_);
                                lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3854_);
                                v___x_3856_ = v_reuseFailAlloc_3857_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_inc(v_idx_3844_);
                            lean_inc_ref(v_array_3843_);
                            v_isSharedCheck_3875_ = (!lean_is_exclusive(v_snd_3837_)) as u8;
                            if v_isSharedCheck_3875_ == 0 {
                                v_unused_3876_ = lean_ctor_get(v_snd_3837_, 1);
                                lean_dec(v_unused_3876_);
                                v_unused_3877_ = lean_ctor_get(v_snd_3837_, 0);
                                lean_dec(v_unused_3877_);
                                v___x_3859_ = v_snd_3837_;
                                v_isShared_3860_ = v_isSharedCheck_3875_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v_snd_3837_);
                                v___x_3859_ = lean_box(0);
                                v_isShared_3860_ = v_isSharedCheck_3875_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_fst_3836_);
                    v___x_3878_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
                    if v_isShared_3840_ == 0 {
                        lean_ctor_set_tag(v___x_3839_, 1);
                        lean_ctor_set(v___x_3839_, 1, v___x_3878_);
                        lean_ctor_set(v___x_3839_, 0, v_snd_3837_);
                        v___x_3880_ = v___x_3839_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_snd_3837_);
                        lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3878_);
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
                lean_dec(v_idx_3844_);
                lean_inc(v___x_3861_);
                lean_inc_ref(v_array_3843_);
                if v_isShared_3860_ == 0 {
                    lean_ctor_set(v___x_3859_, 1, v___x_3861_);
                    v___x_3863_ = v___x_3859_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_array_3843_);
                    lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3861_);
                    v___x_3863_ = v_reuseFailAlloc_3874_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3864_ = lean_nat_dec_lt(v___x_3861_, v___x_3845_);
                if v___x_3864_ == 0 {
                    lean_dec(v___x_3861_);
                    lean_dec_ref(v_array_3843_);
                    lean_dec(v_fst_3836_);
                    v___x_3865_ = lean_box(0);
                    if v_isShared_3840_ == 0 {
                        lean_ctor_set_tag(v___x_3839_, 1);
                        lean_ctor_set(v___x_3839_, 1, v___x_3865_);
                        lean_ctor_set(v___x_3839_, 0, v___x_3863_);
                        v___x_3867_ = v___x_3839_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3863_);
                        lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3865_);
                        v___x_3867_ = v_reuseFailAlloc_3868_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3839_);
                    v___x_3869_ = lean_byte_array_fget(v_array_3843_, v___x_3861_);
                    lean_dec(v___x_3861_);
                    lean_dec_ref(v_array_3843_);
                    v___x_3870_ = lean_uint8_once(
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
                        lean_dec(v_fst_3836_);
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
    mut v_acc_3895_: *mut LeanObject,
    mut v_a_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u8 = 0;
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3911_: u8 = 0;
    let mut v___x_3912_: u8 = 0;
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: u8 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: u8 = 0;
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3897_ = lean_ctor_get(v_a_3896_, 0);
                v_idx_3898_ = lean_ctor_get(v_a_3896_, 1);
                lean_inc(v_idx_3898_);
                v___x_3908_ = lean_byte_array_size(v_array_3897_);
                v___x_3909_ = lean_nat_dec_lt(v_idx_3898_, v___x_3908_);
                if v___x_3909_ == 0 {
                    v___x_3910_ = lean_box(0);
                    lean_inc(v_idx_3898_);
                    v_pos_3900_ = v_a_3896_;
                    v_idx_3901_ = v_idx_3898_;
                    v_err_3902_ = v___x_3910_;
                    state = 1;
                    continue;
                } else {
                    v_c_3911_ = lean_byte_array_fget(v_array_3897_, v_idx_3898_);
                    v___x_3912_ = lean_uint8_once(
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
                        v___x_3914_ = lean_unsigned_to_nat(1);
                        v___x_3915_ = lean_nat_add(v_idx_3898_, v___x_3914_);
                        lean_inc_ref(v_array_3897_);
                        v_it_x27_3916_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_it_x27_3916_, 0, v_array_3897_);
                        lean_ctor_set(v_it_x27_3916_, 1, v___x_3915_);
                        v___x_3922_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2), core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once), _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2);
                        v___x_3923_ = lean_uint8_dec_eq(v_c_3911_, v___x_3922_);
                        if v___x_3923_ == 0 {
                            v___x_3924_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once), _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
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
                lean_dec(v_idx_3901_);
                lean_dec(v_idx_3898_);
                if v___x_3903_ == 0 {
                    lean_dec_ref(v_acc_3895_);
                    lean_inc(v_err_3902_);
                    v___x_3904_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3904_, 0, v_pos_3900_);
                    lean_ctor_set(v___x_3904_, 1, v_err_3902_);
                    return v___x_3904_;
                } else {
                    v___x_3905_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3905_, 0, v_pos_3900_);
                    lean_ctor_set(v___x_3905_, 1, v_acc_3895_);
                    return v___x_3905_;
                }
            }
            2 => {
                v___x_3907_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1;
                lean_inc(v_idx_3898_);
                v_pos_3900_ = v_a_3896_;
                v_idx_3901_ = v_idx_3898_;
                v_err_3902_ = v___x_3907_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_3918_ == 0 {
                    lean_dec_ref_known(v_it_x27_3916_, 2);
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_idx_3898_);
                    lean_dec_ref(v_a_3896_);
                    v___x_3919_ = lean_box((v_c_3911_) as usize);
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
    mut v___x_3926_: *mut LeanObject,
    mut v_acc_3927_: *mut LeanObject,
    mut v_a_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2518__boxed_3929_: u8 = 0;
    let mut v_res_3930_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518__boxed_3929_ = (lean_unbox(v___x_3926_) as u8);
    v_res_3930_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_2518__boxed_3929_, v_acc_3927_, v_a_3928_);
    return v_res_3930_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(
    mut v_actions_3933_: *mut LeanObject,
    mut v_a_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3954_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_array_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: u8 = 0;
    let mut v___x_3967_: u8 = 0;
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v_pos_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_array_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v_utf8_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    let mut v_got_4016_: u8 = 0;
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_unused_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4031_: u8 = 0;
    let mut v_pos_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4040_: u8 = 0;
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v_array_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v_utf8_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u8 = 0;
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: u8 = 0;
    let mut v_got_4064_: u8 = 0;
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4078_: u8 = 0;
    let mut v_unused_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4087_: u8 = 0;
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3959_ = lean_ctor_get(v_a_3934_, 0);
                v_idx_3960_ = lean_ctor_get(v_a_3934_, 1);
                v___x_3961_ = lean_byte_array_size(v_array_3959_);
                v___x_3962_ = lean_nat_dec_lt(v_idx_3960_, v___x_3961_);
                if v___x_3962_ == 0 {
                    lean_dec_ref(v_actions_3933_);
                    v___x_3963_ = lean_box(0);
                    v___x_3964_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3964_, 0, v_a_3934_);
                    lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                    return v___x_3964_;
                } else {
                    v___x_3965_ = lean_byte_array_fget(v_array_3959_, v_idx_3960_);
                    v___x_3966_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once), _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
                    v___x_3967_ = lean_uint8_dec_eq(v___x_3965_, v___x_3966_);
                    if v___x_3967_ == 0 {
                        v___x_3968_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_3934_);
                        if lean_obj_tag(v___x_3968_) == 0 {
                            v_pos_3969_ = lean_ctor_get(v___x_3968_, 0);
                            v_res_3970_ = lean_ctor_get(v___x_3968_, 1);
                            v_isSharedCheck_4031_ = (!lean_is_exclusive(v___x_3968_)) as u8;
                            if v_isSharedCheck_4031_ == 0 {
                                v___x_3972_ = v___x_3968_;
                                v_isShared_3973_ = v_isSharedCheck_4031_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_res_3970_);
                                lean_inc(v_pos_3969_);
                                lean_dec(v___x_3968_);
                                v___x_3972_ = lean_box(0);
                                v_isShared_3973_ = v_isSharedCheck_4031_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_actions_3933_);
                            v_pos_4032_ = lean_ctor_get(v___x_3968_, 0);
                            v_err_4033_ = lean_ctor_get(v___x_3968_, 1);
                            v_isSharedCheck_4040_ = (!lean_is_exclusive(v___x_3968_)) as u8;
                            if v_isSharedCheck_4040_ == 0 {
                                v___x_4035_ = v___x_3968_;
                                v_isShared_4036_ = v_isSharedCheck_4040_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_err_4033_);
                                lean_inc(v_pos_4032_);
                                lean_dec(v___x_3968_);
                                v___x_4035_ = lean_box(0);
                                v_isShared_4036_ = v_isSharedCheck_4040_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        v___x_4041_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0;
                        v___x_4042_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_3965_, v___x_4041_, v_a_3934_);
                        if lean_obj_tag(v___x_4042_) == 0 {
                            v_pos_4043_ = lean_ctor_get(v___x_4042_, 0);
                            v_isSharedCheck_4081_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4081_ == 0 {
                                v_unused_4082_ = lean_ctor_get(v___x_4042_, 1);
                                lean_dec(v_unused_4082_);
                                v___x_4045_ = v___x_4042_;
                                v_isShared_4046_ = v_isSharedCheck_4081_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_pos_4043_);
                                lean_dec(v___x_4042_);
                                v___x_4045_ = lean_box(0);
                                v_isShared_4046_ = v_isSharedCheck_4081_;
                                state = 18;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_actions_3933_);
                            v_pos_4083_ = lean_ctor_get(v___x_4042_, 0);
                            v_err_4084_ = lean_ctor_get(v___x_4042_, 1);
                            v_isSharedCheck_4091_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4091_ == 0 {
                                v___x_4086_ = v___x_4042_;
                                v_isShared_4087_ = v_isSharedCheck_4091_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_err_4084_);
                                lean_inc(v_pos_4083_);
                                lean_dec(v___x_4042_);
                                v___x_4086_ = lean_box(0);
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
                lean_dec_ref(v_array_3937_);
                v___x_3940_ = lean_nat_dec_lt(v_idx_3938_, v___x_3939_);
                lean_dec(v_idx_3938_);
                if v___x_3940_ == 0 {
                    v___x_3941_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3941_, 0, v_pos_3936_);
                    lean_ctor_set(v___x_3941_, 1, v_actions_3933_);
                    return v___x_3941_;
                } else {
                    v_a_3934_ = v_pos_3936_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_array_3945_ = lean_ctor_get(v_pos_3944_, 0);
                lean_inc_ref(v_array_3945_);
                v_idx_3946_ = lean_ctor_get(v_pos_3944_, 1);
                lean_inc(v_idx_3946_);
                v_pos_3936_ = v_pos_3944_;
                v_array_3937_ = v_array_3945_;
                v_idx_3938_ = v_idx_3946_;
                state = 1;
                continue;
            }
            3 => {
                if lean_obj_tag(v___y_3948_) == 0 {
                    v_pos_3949_ = lean_ctor_get(v___y_3948_, 0);
                    lean_inc(v_pos_3949_);
                    lean_dec_ref_known(v___y_3948_, 2);
                    v_pos_3944_ = v_pos_3949_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_actions_3933_);
                    v_pos_3950_ = lean_ctor_get(v___y_3948_, 0);
                    v_err_3951_ = lean_ctor_get(v___y_3948_, 1);
                    v_isSharedCheck_3958_ = (!lean_is_exclusive(v___y_3948_)) as u8;
                    if v_isSharedCheck_3958_ == 0 {
                        v___x_3953_ = v___y_3948_;
                        v_isShared_3954_ = v_isSharedCheck_3958_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_err_3951_);
                        lean_inc(v_pos_3950_);
                        lean_dec(v___y_3948_);
                        v___x_3953_ = lean_box(0);
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
                    v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_pos_3950_);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_err_3951_);
                    v___x_3956_ = v_reuseFailAlloc_3957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3956_;
            }
            6 => {
                v_array_4001_ = lean_ctor_get(v_pos_3969_, 0);
                v_idx_4002_ = lean_ctor_get(v_pos_3969_, 1);
                lean_inc(v_idx_4002_);
                v___x_4011_ = lean_byte_array_size(v_array_4001_);
                v___x_4012_ = lean_nat_dec_lt(v_idx_4002_, v___x_4011_);
                if v___x_4012_ == 0 {
                    v___x_4013_ = lean_box(0);
                    lean_inc(v_pos_3969_);
                    v___x_4014_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4014_, 0, v_pos_3969_);
                    lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                    lean_inc(v_idx_4002_);
                    v___y_4004_ = v___x_4014_;
                    v_pos_4005_ = v_pos_3969_;
                    v_idx_4006_ = v_idx_4002_;
                    state = 13;
                    continue;
                } else {
                    v___x_4015_ = lean_uint8_once(
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
                        v___x_4018_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9,
                        );
                        lean_inc(v_pos_3969_);
                        v___x_4019_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4019_, 0, v_pos_3969_);
                        lean_ctor_set(v___x_4019_, 1, v___x_4018_);
                        lean_inc(v_idx_4002_);
                        v___y_4004_ = v___x_4019_;
                        v_pos_4005_ = v_pos_3969_;
                        v_idx_4006_ = v_idx_4002_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc_ref(v_array_4001_);
                        v_isSharedCheck_4028_ = (!lean_is_exclusive(v_pos_3969_)) as u8;
                        if v_isSharedCheck_4028_ == 0 {
                            v_unused_4029_ = lean_ctor_get(v_pos_3969_, 1);
                            lean_dec(v_unused_4029_);
                            v_unused_4030_ = lean_ctor_get(v_pos_3969_, 0);
                            lean_dec(v_unused_4030_);
                            v___x_4021_ = v_pos_3969_;
                            v_isShared_4022_ = v_isSharedCheck_4028_;
                            state = 14;
                            continue;
                        } else {
                            lean_dec(v_pos_3969_);
                            v___x_4021_ = lean_box(0);
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
                lean_dec_ref(v_array_3976_);
                v___x_3980_ = lean_nat_dec_lt(v_idx_3977_, v___x_3979_);
                lean_dec(v_idx_3977_);
                if v___x_3980_ == 0 {
                    if v_isShared_3973_ == 0 {
                        lean_ctor_set(v___x_3972_, 1, v___x_3978_);
                        lean_ctor_set(v___x_3972_, 0, v_pos_3975_);
                        v___x_3982_ = v___x_3972_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_pos_3975_);
                        lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3978_);
                        v___x_3982_ = v_reuseFailAlloc_3983_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3972_);
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
                v_array_3987_ = lean_ctor_get(v_pos_3986_, 0);
                lean_inc_ref(v_array_3987_);
                v_idx_3988_ = lean_ctor_get(v_pos_3986_, 1);
                lean_inc(v_idx_3988_);
                v_pos_3975_ = v_pos_3986_;
                v_array_3976_ = v_array_3987_;
                v_idx_3977_ = v_idx_3988_;
                state = 7;
                continue;
            }
            10 => {
                if lean_obj_tag(v___y_3990_) == 0 {
                    v_pos_3991_ = lean_ctor_get(v___y_3990_, 0);
                    lean_inc(v_pos_3991_);
                    lean_dec_ref_known(v___y_3990_, 2);
                    v_pos_3986_ = v_pos_3991_;
                    state = 9;
                    continue;
                } else {
                    lean_del_object(v___x_3972_);
                    lean_dec(v_res_3970_);
                    lean_dec_ref(v_actions_3933_);
                    v_pos_3992_ = lean_ctor_get(v___y_3990_, 0);
                    v_err_3993_ = lean_ctor_get(v___y_3990_, 1);
                    v_isSharedCheck_4000_ = (!lean_is_exclusive(v___y_3990_)) as u8;
                    if v_isSharedCheck_4000_ == 0 {
                        v___x_3995_ = v___y_3990_;
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_err_3993_);
                        lean_inc(v_pos_3992_);
                        lean_dec(v___y_3990_);
                        v___x_3995_ = lean_box(0);
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
                    v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_pos_3992_);
                    lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_err_3993_);
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
                lean_dec(v_idx_4006_);
                lean_dec(v_idx_4002_);
                if v___x_4007_ == 0 {
                    lean_dec_ref(v_pos_4005_);
                    v___y_3990_ = v___y_4004_;
                    state = 10;
                    continue;
                } else {
                    lean_dec_ref(v___y_4004_);
                    v_utf8_4008_ = lean_obj_once(
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
                    if lean_obj_tag(v___x_4009_) == 0 {
                        v_pos_4010_ = lean_ctor_get(v___x_4009_, 0);
                        lean_inc(v_pos_4010_);
                        lean_dec_ref_known(v___x_4009_, 2);
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
                v___x_4023_ = lean_unsigned_to_nat(1);
                v___x_4024_ = lean_nat_add(v_idx_4002_, v___x_4023_);
                lean_dec(v_idx_4002_);
                lean_inc(v___x_4024_);
                lean_inc_ref(v_array_4001_);
                if v_isShared_4022_ == 0 {
                    lean_ctor_set(v___x_4021_, 1, v___x_4024_);
                    v___x_4026_ = v___x_4021_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_array_4001_);
                    lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4024_);
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
                    v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_pos_4032_);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_err_4033_);
                    v___x_4038_ = v_reuseFailAlloc_4039_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4038_;
            }
            18 => {
                v_array_4047_ = lean_ctor_get(v_pos_4043_, 0);
                v_idx_4048_ = lean_ctor_get(v_pos_4043_, 1);
                lean_inc(v_idx_4048_);
                v___x_4057_ = lean_byte_array_size(v_array_4047_);
                v___x_4058_ = lean_nat_dec_lt(v_idx_4048_, v___x_4057_);
                if v___x_4058_ == 0 {
                    v___x_4059_ = lean_box(0);
                    lean_inc(v_pos_4043_);
                    if v_isShared_4046_ == 0 {
                        lean_ctor_set_tag(v___x_4045_, 1);
                        lean_ctor_set(v___x_4045_, 1, v___x_4059_);
                        v___x_4061_ = v___x_4045_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_pos_4043_);
                        lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4059_);
                        v___x_4061_ = v_reuseFailAlloc_4062_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_4063_ = lean_uint8_once(
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
                        v___x_4066_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9,
                        );
                        lean_inc(v_pos_4043_);
                        if v_isShared_4046_ == 0 {
                            lean_ctor_set_tag(v___x_4045_, 1);
                            lean_ctor_set(v___x_4045_, 1, v___x_4066_);
                            v___x_4068_ = v___x_4045_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_pos_4043_);
                            lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4066_);
                            v___x_4068_ = v_reuseFailAlloc_4069_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_array_4047_);
                        lean_del_object(v___x_4045_);
                        v_isSharedCheck_4078_ = (!lean_is_exclusive(v_pos_4043_)) as u8;
                        if v_isSharedCheck_4078_ == 0 {
                            v_unused_4079_ = lean_ctor_get(v_pos_4043_, 1);
                            lean_dec(v_unused_4079_);
                            v_unused_4080_ = lean_ctor_get(v_pos_4043_, 0);
                            lean_dec(v_unused_4080_);
                            v___x_4071_ = v_pos_4043_;
                            v_isShared_4072_ = v_isSharedCheck_4078_;
                            state = 22;
                            continue;
                        } else {
                            lean_dec(v_pos_4043_);
                            v___x_4071_ = lean_box(0);
                            v_isShared_4072_ = v_isSharedCheck_4078_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            19 => {
                v___x_4053_ = lean_nat_dec_eq(v_idx_4048_, v_idx_4052_);
                lean_dec(v_idx_4052_);
                lean_dec(v_idx_4048_);
                if v___x_4053_ == 0 {
                    lean_dec_ref(v_pos_4051_);
                    v___y_3948_ = v___y_4050_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v___y_4050_);
                    v_utf8_4054_ = lean_obj_once(
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
                    if lean_obj_tag(v___x_4055_) == 0 {
                        v_pos_4056_ = lean_ctor_get(v___x_4055_, 0);
                        lean_inc(v_pos_4056_);
                        lean_dec_ref_known(v___x_4055_, 2);
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
                lean_inc(v_idx_4048_);
                v___y_4050_ = v___x_4061_;
                v_pos_4051_ = v_pos_4043_;
                v_idx_4052_ = v_idx_4048_;
                state = 19;
                continue;
            }
            21 => {
                lean_inc(v_idx_4048_);
                v___y_4050_ = v___x_4068_;
                v_pos_4051_ = v_pos_4043_;
                v_idx_4052_ = v_idx_4048_;
                state = 19;
                continue;
            }
            22 => {
                v___x_4073_ = lean_unsigned_to_nat(1);
                v___x_4074_ = lean_nat_add(v_idx_4048_, v___x_4073_);
                lean_dec(v_idx_4048_);
                lean_inc(v___x_4074_);
                lean_inc_ref(v_array_4047_);
                if v_isShared_4072_ == 0 {
                    lean_ctor_set(v___x_4071_, 1, v___x_4074_);
                    v___x_4076_ = v___x_4071_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_array_4047_);
                    lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4074_);
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
                    v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_pos_4083_);
                    lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_err_4084_);
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
    mut v_a_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0;
    v___x_4096_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_4095_, v_a_4094_);
    return v___x_4096_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0()
-> *mut LeanObject {
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    v___x_4097_ = lean_unsigned_to_nat(0);
    v___x_4098_ = l_Nat_reprFast(v___x_4097_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1()
-> *mut LeanObject {
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    v___x_4099_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    v___x_4102_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
    v___x_4103_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    v___x_4105_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2_once
        ),
        _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2,
    );
    v___x_4106_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4106_, 0, v___x_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(
    mut v_a_4107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: u8 = 0;
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: u8 = 0;
    let mut v_got_4115_: u8 = 0;
    let mut v___x_4116_: u8 = 0;
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_unused_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4108_ = lean_ctor_get(v_a_4107_, 0);
                v_idx_4109_ = lean_ctor_get(v_a_4107_, 1);
                v___x_4110_ = lean_byte_array_size(v_array_4108_);
                v___x_4111_ = lean_nat_dec_lt(v_idx_4109_, v___x_4110_);
                if v___x_4111_ == 0 {
                    v___x_4112_ = lean_box(0);
                    v___x_4113_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4113_, 0, v_a_4107_);
                    lean_ctor_set(v___x_4113_, 1, v___x_4112_);
                    return v___x_4113_;
                } else {
                    v___x_4114_ = 0;
                    v_got_4115_ = lean_byte_array_fget(v_array_4108_, v_idx_4109_);
                    v___x_4116_ = lean_uint8_dec_eq(v_got_4115_, v___x_4114_);
                    if v___x_4116_ == 0 {
                        v___x_4117_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        v___x_4118_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4118_, 0, v_a_4107_);
                        lean_ctor_set(v___x_4118_, 1, v___x_4117_);
                        return v___x_4118_;
                    } else {
                        lean_inc(v_idx_4109_);
                        lean_inc_ref(v_array_4108_);
                        v_isSharedCheck_4129_ = (!lean_is_exclusive(v_a_4107_)) as u8;
                        if v_isSharedCheck_4129_ == 0 {
                            v_unused_4130_ = lean_ctor_get(v_a_4107_, 1);
                            lean_dec(v_unused_4130_);
                            v_unused_4131_ = lean_ctor_get(v_a_4107_, 0);
                            lean_dec(v_unused_4131_);
                            v___x_4120_ = v_a_4107_;
                            v_isShared_4121_ = v_isSharedCheck_4129_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_4107_);
                            v___x_4120_ = lean_box(0);
                            v_isShared_4121_ = v_isSharedCheck_4129_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4122_ = lean_unsigned_to_nat(1);
                v___x_4123_ = lean_nat_add(v_idx_4109_, v___x_4122_);
                lean_dec(v_idx_4109_);
                if v_isShared_4121_ == 0 {
                    lean_ctor_set(v___x_4120_, 1, v___x_4123_);
                    v___x_4125_ = v___x_4120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_array_4108_);
                    lean_ctor_set(v_reuseFailAlloc_4128_, 1, v___x_4123_);
                    v___x_4125_ = v_reuseFailAlloc_4128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4126_ = lean_box(0);
                v___x_4127_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4127_, 0, v___x_4125_);
                lean_ctor_set(v___x_4127_, 1, v___x_4126_);
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
    mut v_a_4142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v_c_4152_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4158_: u64 = 0;
    let mut v___y_4159_: u8 = 0;
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: u64 = 0;
    let mut v___x_4193_: u8 = 0;
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: u8 = 0;
    let mut v___x_4196_: u8 = 0;
    let mut v___x_4197_: u8 = 0;
    let mut v_reuseFailAlloc_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_unused_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4143_ = lean_ctor_get(v_a_4142_, 0);
                v_idx_4144_ = lean_ctor_get(v_a_4142_, 1);
                v___x_4145_ = lean_byte_array_size(v_array_4143_);
                v___x_4146_ = lean_nat_dec_lt(v_idx_4144_, v___x_4145_);
                if v___x_4146_ == 0 {
                    v___x_4147_ = lean_box(0);
                    v___x_4148_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4148_, 0, v_a_4142_);
                    lean_ctor_set(v___x_4148_, 1, v___x_4147_);
                    return v___x_4148_;
                } else {
                    lean_inc(v_idx_4144_);
                    lean_inc_ref(v_array_4143_);
                    v_isSharedCheck_4199_ = (!lean_is_exclusive(v_a_4142_)) as u8;
                    if v_isSharedCheck_4199_ == 0 {
                        v_unused_4200_ = lean_ctor_get(v_a_4142_, 1);
                        lean_dec(v_unused_4200_);
                        v_unused_4201_ = lean_ctor_get(v_a_4142_, 0);
                        lean_dec(v_unused_4201_);
                        v___x_4150_ = v_a_4142_;
                        v_isShared_4151_ = v_isSharedCheck_4199_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_4142_);
                        v___x_4150_ = lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4199_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_c_4152_ = lean_byte_array_fget(v_array_4143_, v_idx_4144_);
                v___x_4153_ = lean_unsigned_to_nat(1);
                v___x_4154_ = lean_nat_add(v_idx_4144_, v___x_4153_);
                lean_dec(v_idx_4144_);
                if v_isShared_4151_ == 0 {
                    lean_ctor_set(v___x_4150_, 1, v___x_4154_);
                    v_it_x27_4156_ = v___x_4150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_array_4143_);
                    lean_ctor_set(v_reuseFailAlloc_4198_, 1, v___x_4154_);
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
                    v___x_4194_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4);
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
                    v___x_4162_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4162_, 0, v_it_x27_4156_);
                    lean_ctor_set(v___x_4162_, 1, v___x_4161_);
                    return v___x_4162_;
                } else {
                    v___x_4163_ = lean_uint64_to_nat(v___y_4158_);
                    v___x_4164_ = lean_nat_to_int(v___x_4163_);
                    v___x_4165_ = lean_int_neg(v___x_4164_);
                    lean_dec(v___x_4164_);
                    v___x_4166_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4166_, 0, v_it_x27_4156_);
                    lean_ctor_set(v___x_4166_, 1, v___x_4165_);
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
                    v___x_4187_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4187_, 0, v_it_x27_4156_);
                    lean_ctor_set(v___x_4187_, 1, v___x_4186_);
                    return v___x_4187_;
                }
            }
            5 => {
                if v___y_4189_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_4190_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3;
                    v___x_4191_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4191_, 0, v_it_x27_4156_);
                    lean_ctor_set(v___x_4191_, 1, v___x_4190_);
                    return v___x_4191_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(
    mut v_uidx_4202_: *mut LeanObject,
    mut v_shift_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uidx_boxed_4205_: u64 = 0;
    let mut v_shift_boxed_4206_: u64 = 0;
    let mut v_res_4207_: *mut LeanObject = core::ptr::null_mut();
    v_uidx_boxed_4205_ = lean_unbox_uint64(v_uidx_4202_);
    lean_dec_ref(v_uidx_4202_);
    v_shift_boxed_4206_ = lean_unbox_uint64(v_shift_4203_);
    lean_dec_ref(v_shift_4203_);
    v_res_4207_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_4205_, v_shift_boxed_4206_, v_a_4204_);
    return v_res_4207_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(
    mut v_a_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4209_: u64 = 0;
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    v___x_4209_ = 0u64;
    v___x_4210_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_4209_, v___x_4209_, v_a_4208_);
    return v___x_4210_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(
    mut v_a_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: u8 = 0;
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut v_pos_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4215_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4214_);
                if lean_obj_tag(v___x_4215_) == 0 {
                    v_pos_4216_ = lean_ctor_get(v___x_4215_, 0);
                    v_res_4217_ = lean_ctor_get(v___x_4215_, 1);
                    v_isSharedCheck_4231_ = (!lean_is_exclusive(v___x_4215_)) as u8;
                    if v_isSharedCheck_4231_ == 0 {
                        v___x_4219_ = v___x_4215_;
                        v_isShared_4220_ = v_isSharedCheck_4231_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4217_);
                        lean_inc(v_pos_4216_);
                        lean_dec(v___x_4215_);
                        v___x_4219_ = lean_box(0);
                        v_isShared_4220_ = v_isSharedCheck_4231_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4232_ = lean_ctor_get(v___x_4215_, 0);
                    v_err_4233_ = lean_ctor_get(v___x_4215_, 1);
                    v_isSharedCheck_4240_ = (!lean_is_exclusive(v___x_4215_)) as u8;
                    if v_isSharedCheck_4240_ == 0 {
                        v___x_4235_ = v___x_4215_;
                        v_isShared_4236_ = v_isSharedCheck_4240_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_err_4233_);
                        lean_inc(v_pos_4232_);
                        lean_dec(v___x_4215_);
                        v___x_4235_ = lean_box(0);
                        v_isShared_4236_ = v_isSharedCheck_4240_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4221_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4222_ = lean_int_dec_lt(v_res_4217_, v___x_4221_);
                if v___x_4222_ == 0 {
                    lean_dec(v_res_4217_);
                    v___x_4223_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
                    if v_isShared_4220_ == 0 {
                        lean_ctor_set_tag(v___x_4219_, 1);
                        lean_ctor_set(v___x_4219_, 1, v___x_4223_);
                        v___x_4225_ = v___x_4219_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_pos_4216_);
                        lean_ctor_set(v_reuseFailAlloc_4226_, 1, v___x_4223_);
                        v___x_4225_ = v_reuseFailAlloc_4226_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4227_ = lean_nat_abs(v_res_4217_);
                    lean_dec(v_res_4217_);
                    if v_isShared_4220_ == 0 {
                        lean_ctor_set(v___x_4219_, 1, v___x_4227_);
                        v___x_4229_ = v___x_4219_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_pos_4216_);
                        lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4227_);
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
                    v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_pos_4232_);
                    lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_err_4233_);
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
    mut v_a_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4261_: u8 = 0;
    let mut v_pos_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4244_);
                if lean_obj_tag(v___x_4245_) == 0 {
                    v_pos_4246_ = lean_ctor_get(v___x_4245_, 0);
                    v_res_4247_ = lean_ctor_get(v___x_4245_, 1);
                    v_isSharedCheck_4261_ = (!lean_is_exclusive(v___x_4245_)) as u8;
                    if v_isSharedCheck_4261_ == 0 {
                        v___x_4249_ = v___x_4245_;
                        v_isShared_4250_ = v_isSharedCheck_4261_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4247_);
                        lean_inc(v_pos_4246_);
                        lean_dec(v___x_4245_);
                        v___x_4249_ = lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4261_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4262_ = lean_ctor_get(v___x_4245_, 0);
                    v_err_4263_ = lean_ctor_get(v___x_4245_, 1);
                    v_isSharedCheck_4270_ = (!lean_is_exclusive(v___x_4245_)) as u8;
                    if v_isSharedCheck_4270_ == 0 {
                        v___x_4265_ = v___x_4245_;
                        v_isShared_4266_ = v_isSharedCheck_4270_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_err_4263_);
                        lean_inc(v_pos_4262_);
                        lean_dec(v___x_4245_);
                        v___x_4265_ = lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4270_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4251_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4252_ = lean_int_dec_lt(v___x_4251_, v_res_4247_);
                if v___x_4252_ == 0 {
                    lean_dec(v_res_4247_);
                    v___x_4253_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4250_ == 0 {
                        lean_ctor_set_tag(v___x_4249_, 1);
                        lean_ctor_set(v___x_4249_, 1, v___x_4253_);
                        v___x_4255_ = v___x_4249_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_pos_4246_);
                        lean_ctor_set(v_reuseFailAlloc_4256_, 1, v___x_4253_);
                        v___x_4255_ = v_reuseFailAlloc_4256_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4257_ = lean_nat_abs(v_res_4247_);
                    lean_dec(v_res_4247_);
                    if v_isShared_4250_ == 0 {
                        lean_ctor_set(v___x_4249_, 1, v___x_4257_);
                        v___x_4259_ = v___x_4249_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_pos_4246_);
                        lean_ctor_set(v_reuseFailAlloc_4260_, 1, v___x_4257_);
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
                    v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_pos_4262_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_err_4263_);
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
    mut v_a_4271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: u8 = 0;
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_pos_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4272_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4271_);
                if lean_obj_tag(v___x_4272_) == 0 {
                    v_pos_4273_ = lean_ctor_get(v___x_4272_, 0);
                    v_res_4274_ = lean_ctor_get(v___x_4272_, 1);
                    v_isSharedCheck_4288_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4288_ == 0 {
                        v___x_4276_ = v___x_4272_;
                        v_isShared_4277_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4274_);
                        lean_inc(v_pos_4273_);
                        lean_dec(v___x_4272_);
                        v___x_4276_ = lean_box(0);
                        v_isShared_4277_ = v_isSharedCheck_4288_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4289_ = lean_ctor_get(v___x_4272_, 0);
                    v_err_4290_ = lean_ctor_get(v___x_4272_, 1);
                    v_isSharedCheck_4297_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4297_ == 0 {
                        v___x_4292_ = v___x_4272_;
                        v_isShared_4293_ = v_isSharedCheck_4297_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_err_4290_);
                        lean_inc(v_pos_4289_);
                        lean_dec(v___x_4272_);
                        v___x_4292_ = lean_box(0);
                        v_isShared_4293_ = v_isSharedCheck_4297_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4279_ = lean_int_dec_lt(v___x_4278_, v_res_4274_);
                if v___x_4279_ == 0 {
                    lean_dec(v_res_4274_);
                    v___x_4280_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4277_ == 0 {
                        lean_ctor_set_tag(v___x_4276_, 1);
                        lean_ctor_set(v___x_4276_, 1, v___x_4280_);
                        v___x_4282_ = v___x_4276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_pos_4273_);
                        lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___x_4280_);
                        v___x_4282_ = v_reuseFailAlloc_4283_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4284_ = lean_nat_abs(v_res_4274_);
                    lean_dec(v_res_4274_);
                    if v_isShared_4277_ == 0 {
                        lean_ctor_set(v___x_4276_, 1, v___x_4284_);
                        v___x_4286_ = v___x_4276_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_pos_4273_);
                        lean_ctor_set(v_reuseFailAlloc_4287_, 1, v___x_4284_);
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
                    v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_pos_4289_);
                    lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_err_4290_);
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
    mut v_parser_4298_: *mut LeanObject,
    mut v_acc_4299_: *mut LeanObject,
    mut v_a_4300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: u8 = 0;
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4301_ = lean_ctor_get(v_a_4300_, 0);
                v_idx_4302_ = lean_ctor_get(v_a_4300_, 1);
                v___x_4303_ = lean_byte_array_size(v_array_4301_);
                v___x_4304_ = lean_nat_dec_lt(v_idx_4302_, v___x_4303_);
                if v___x_4304_ == 0 {
                    lean_dec_ref(v_acc_4299_);
                    lean_dec_ref(v_parser_4298_);
                    v___x_4305_ = lean_box(0);
                    v___x_4306_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4306_, 0, v_a_4300_);
                    lean_ctor_set(v___x_4306_, 1, v___x_4305_);
                    return v___x_4306_;
                } else {
                    v___x_4307_ = lean_byte_array_fget(v_array_4301_, v_idx_4302_);
                    v___x_4308_ = 0;
                    v___x_4309_ = lean_uint8_dec_eq(v___x_4307_, v___x_4308_);
                    if v___x_4309_ == 0 {
                        lean_inc_ref(v_parser_4298_);
                        v___x_4310_ = lean_apply_1(v_parser_4298_, v_a_4300_);
                        if lean_obj_tag(v___x_4310_) == 0 {
                            v_pos_4311_ = lean_ctor_get(v___x_4310_, 0);
                            lean_inc(v_pos_4311_);
                            v_res_4312_ = lean_ctor_get(v___x_4310_, 1);
                            lean_inc(v_res_4312_);
                            lean_dec_ref_known(v___x_4310_, 2);
                            v___x_4313_ = lean_array_push(v_acc_4299_, v_res_4312_);
                            v_acc_4299_ = v___x_4313_;
                            v_a_4300_ = v_pos_4311_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_acc_4299_);
                            lean_dec_ref(v_parser_4298_);
                            v_pos_4315_ = lean_ctor_get(v___x_4310_, 0);
                            v_err_4316_ = lean_ctor_get(v___x_4310_, 1);
                            v_isSharedCheck_4323_ = (!lean_is_exclusive(v___x_4310_)) as u8;
                            if v_isSharedCheck_4323_ == 0 {
                                v___x_4318_ = v___x_4310_;
                                v_isShared_4319_ = v_isSharedCheck_4323_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_err_4316_);
                                lean_inc(v_pos_4315_);
                                lean_dec(v___x_4310_);
                                v___x_4318_ = lean_box(0);
                                v_isShared_4319_ = v_isSharedCheck_4323_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_parser_4298_);
                        v___x_4324_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4324_, 0, v_a_4300_);
                        lean_ctor_set(v___x_4324_, 1, v_acc_4299_);
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
                    v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_pos_4315_);
                    lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_err_4316_);
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
    mut v_00_u03b1_4325_: *mut LeanObject,
    mut v_parser_4326_: *mut LeanObject,
    mut v_acc_4327_: *mut LeanObject,
    mut v_a_4328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    v___x_4329_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_4326_, v_acc_4327_, v_a_4328_);
    return v___x_4329_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(
    mut v_parser_4332_: *mut LeanObject,
    mut v_a_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    v___x_4334_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0;
    v___x_4335_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_4332_, v___x_4334_, v_a_4333_);
    return v___x_4335_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(
    mut v_00_u03b1_4336_: *mut LeanObject,
    mut v_parser_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4339_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_4337_, v_a_4338_);
    return v___x_4339_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(
    mut v_parser_4340_: *mut LeanObject,
    mut v_acc_4341_: *mut LeanObject,
    mut v_a_4342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: u8 = 0;
    let mut v___x_4351_: u8 = 0;
    let mut v___x_4352_: u8 = 0;
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4343_ = lean_ctor_get(v_a_4342_, 0);
                v_idx_4344_ = lean_ctor_get(v_a_4342_, 1);
                v___x_4345_ = lean_byte_array_size(v_array_4343_);
                v___x_4346_ = lean_nat_dec_lt(v_idx_4344_, v___x_4345_);
                if v___x_4346_ == 0 {
                    lean_dec_ref(v_acc_4341_);
                    lean_dec_ref(v_parser_4340_);
                    v___x_4347_ = lean_box(0);
                    v___x_4348_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4348_, 0, v_a_4342_);
                    lean_ctor_set(v___x_4348_, 1, v___x_4347_);
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
                            lean_dec_ref(v_parser_4340_);
                            v___x_4372_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4372_, 0, v_a_4342_);
                            lean_ctor_set(v___x_4372_, 1, v_acc_4341_);
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
                    lean_inc_ref(v_parser_4340_);
                    v___x_4353_ = lean_apply_1(v_parser_4340_, v_a_4342_);
                    if lean_obj_tag(v___x_4353_) == 0 {
                        v_pos_4354_ = lean_ctor_get(v___x_4353_, 0);
                        lean_inc(v_pos_4354_);
                        v_res_4355_ = lean_ctor_get(v___x_4353_, 1);
                        lean_inc(v_res_4355_);
                        lean_dec_ref_known(v___x_4353_, 2);
                        v___x_4356_ = lean_array_push(v_acc_4341_, v_res_4355_);
                        v_acc_4341_ = v___x_4356_;
                        v_a_4342_ = v_pos_4354_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_acc_4341_);
                        lean_dec_ref(v_parser_4340_);
                        v_pos_4358_ = lean_ctor_get(v___x_4353_, 0);
                        v_err_4359_ = lean_ctor_get(v___x_4353_, 1);
                        v_isSharedCheck_4366_ = (!lean_is_exclusive(v___x_4353_)) as u8;
                        if v_isSharedCheck_4366_ == 0 {
                            v___x_4361_ = v___x_4353_;
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_err_4359_);
                            lean_inc(v_pos_4358_);
                            lean_dec(v___x_4353_);
                            v___x_4361_ = lean_box(0);
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_parser_4340_);
                    v___x_4367_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4367_, 0, v_a_4342_);
                    lean_ctor_set(v___x_4367_, 1, v_acc_4341_);
                    return v___x_4367_;
                }
            }
            2 => {
                if v_isShared_4362_ == 0 {
                    v___x_4364_ = v___x_4361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_pos_4358_);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_err_4359_);
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
    mut v_00_u03b1_4373_: *mut LeanObject,
    mut v_parser_4374_: *mut LeanObject,
    mut v_acc_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    v___x_4377_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_4374_, v_acc_4375_, v_a_4376_);
    return v___x_4377_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(
    mut v_parser_4378_: *mut LeanObject,
    mut v_a_4379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0;
    v___x_4381_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_4378_, v___x_4380_, v_a_4379_);
    return v___x_4381_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(
    mut v_00_u03b1_4382_: *mut LeanObject,
    mut v_parser_4383_: *mut LeanObject,
    mut v_a_4384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    v___x_4385_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(
        v_parser_4383_,
        v_a_4384_,
    );
    return v___x_4385_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(
    mut v_a_4386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    v___x_4387_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4388_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_4387_, v_a_4386_);
    return v___x_4388_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(
    mut v_a_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    v___x_4390_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4391_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_4390_, v_a_4389_);
    return v___x_4391_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(
    mut v_acc_4392_: *mut LeanObject,
    mut v_a_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: u8 = 0;
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut v_pos_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: u8 = 0;
    let mut v___x_4432_: u8 = 0;
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4394_ = lean_ctor_get(v_a_4393_, 0);
                v_idx_4395_ = lean_ctor_get(v_a_4393_, 1);
                v___x_4396_ = lean_byte_array_size(v_array_4394_);
                v___x_4397_ = lean_nat_dec_lt(v_idx_4395_, v___x_4396_);
                if v___x_4397_ == 0 {
                    lean_dec_ref(v_acc_4392_);
                    v___x_4398_ = lean_box(0);
                    v___x_4399_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4399_, 0, v_a_4393_);
                    lean_ctor_set(v___x_4399_, 1, v___x_4398_);
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
                            v___x_4434_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4434_, 0, v_a_4393_);
                            lean_ctor_set(v___x_4434_, 1, v_acc_4392_);
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
                    if lean_obj_tag(v___x_4404_) == 0 {
                        v_pos_4405_ = lean_ctor_get(v___x_4404_, 0);
                        v_res_4406_ = lean_ctor_get(v___x_4404_, 1);
                        v_isSharedCheck_4419_ = (!lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4419_ == 0 {
                            v___x_4408_ = v___x_4404_;
                            v_isShared_4409_ = v_isSharedCheck_4419_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_res_4406_);
                            lean_inc(v_pos_4405_);
                            lean_dec(v___x_4404_);
                            v___x_4408_ = lean_box(0);
                            v_isShared_4409_ = v_isSharedCheck_4419_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_acc_4392_);
                        v_pos_4420_ = lean_ctor_get(v___x_4404_, 0);
                        v_err_4421_ = lean_ctor_get(v___x_4404_, 1);
                        v_isSharedCheck_4428_ = (!lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4428_ == 0 {
                            v___x_4423_ = v___x_4404_;
                            v_isShared_4424_ = v_isSharedCheck_4428_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_err_4421_);
                            lean_inc(v_pos_4420_);
                            lean_dec(v___x_4404_);
                            v___x_4423_ = lean_box(0);
                            v_isShared_4424_ = v_isSharedCheck_4428_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_4429_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4429_, 0, v_a_4393_);
                    lean_ctor_set(v___x_4429_, 1, v_acc_4392_);
                    return v___x_4429_;
                }
            }
            2 => {
                v___x_4410_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4411_ = lean_int_dec_lt(v___x_4410_, v_res_4406_);
                if v___x_4411_ == 0 {
                    lean_dec(v_res_4406_);
                    lean_dec_ref(v_acc_4392_);
                    v___x_4412_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4409_ == 0 {
                        lean_ctor_set_tag(v___x_4408_, 1);
                        lean_ctor_set(v___x_4408_, 1, v___x_4412_);
                        v___x_4414_ = v___x_4408_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_pos_4405_);
                        lean_ctor_set(v_reuseFailAlloc_4415_, 1, v___x_4412_);
                        v___x_4414_ = v_reuseFailAlloc_4415_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4408_);
                    v___x_4416_ = lean_nat_abs(v_res_4406_);
                    lean_dec(v_res_4406_);
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
                    v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_pos_4420_);
                    lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_err_4421_);
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
    mut v_a_4435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    v___x_4436_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0;
    v___x_4437_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_4436_, v_a_4435_);
    return v___x_4437_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(
    mut v_a_4438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: u8 = 0;
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut v_pos_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_pos_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4439_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4438_);
                if lean_obj_tag(v___x_4439_) == 0 {
                    v_pos_4440_ = lean_ctor_get(v___x_4439_, 0);
                    v_res_4441_ = lean_ctor_get(v___x_4439_, 1);
                    v_isSharedCheck_4472_ = (!lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4443_ = v___x_4439_;
                        v_isShared_4444_ = v_isSharedCheck_4472_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4441_);
                        lean_inc(v_pos_4440_);
                        lean_dec(v___x_4439_);
                        v___x_4443_ = lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4472_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4473_ = lean_ctor_get(v___x_4439_, 0);
                    v_err_4474_ = lean_ctor_get(v___x_4439_, 1);
                    v_isSharedCheck_4481_ = (!lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4481_ == 0 {
                        v___x_4476_ = v___x_4439_;
                        v_isShared_4477_ = v_isSharedCheck_4481_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_err_4474_);
                        lean_inc(v_pos_4473_);
                        lean_dec(v___x_4439_);
                        v___x_4476_ = lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4481_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4445_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4446_ = lean_int_dec_lt(v_res_4441_, v___x_4445_);
                if v___x_4446_ == 0 {
                    lean_dec(v_res_4441_);
                    v___x_4447_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
                    if v_isShared_4444_ == 0 {
                        lean_ctor_set_tag(v___x_4443_, 1);
                        lean_ctor_set(v___x_4443_, 1, v___x_4447_);
                        v___x_4449_ = v___x_4443_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_pos_4440_);
                        lean_ctor_set(v_reuseFailAlloc_4450_, 1, v___x_4447_);
                        v___x_4449_ = v_reuseFailAlloc_4450_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4443_);
                    v___x_4451_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_4440_);
                    if lean_obj_tag(v___x_4451_) == 0 {
                        v_pos_4452_ = lean_ctor_get(v___x_4451_, 0);
                        v_res_4453_ = lean_ctor_get(v___x_4451_, 1);
                        v_isSharedCheck_4462_ = (!lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4462_ == 0 {
                            v___x_4455_ = v___x_4451_;
                            v_isShared_4456_ = v_isSharedCheck_4462_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_res_4453_);
                            lean_inc(v_pos_4452_);
                            lean_dec(v___x_4451_);
                            v___x_4455_ = lean_box(0);
                            v_isShared_4456_ = v_isSharedCheck_4462_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_4441_);
                        v_pos_4463_ = lean_ctor_get(v___x_4451_, 0);
                        v_err_4464_ = lean_ctor_get(v___x_4451_, 1);
                        v_isSharedCheck_4471_ = (!lean_is_exclusive(v___x_4451_)) as u8;
                        if v_isSharedCheck_4471_ == 0 {
                            v___x_4466_ = v___x_4451_;
                            v_isShared_4467_ = v_isSharedCheck_4471_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_err_4464_);
                            lean_inc(v_pos_4463_);
                            lean_dec(v___x_4451_);
                            v___x_4466_ = lean_box(0);
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
                lean_dec(v_res_4441_);
                v___x_4458_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4458_, 0, v___x_4457_);
                lean_ctor_set(v___x_4458_, 1, v_res_4453_);
                if v_isShared_4456_ == 0 {
                    lean_ctor_set(v___x_4455_, 1, v___x_4458_);
                    v___x_4460_ = v___x_4455_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_pos_4452_);
                    lean_ctor_set(v_reuseFailAlloc_4461_, 1, v___x_4458_);
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
                    v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_pos_4463_);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_err_4464_);
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
                    v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_pos_4473_);
                    lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_err_4474_);
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
    mut v_a_4482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    v___x_4483_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4484_ =
        l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_4483_, v_a_4482_);
    return v___x_4484_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(
    mut v_acc_4485_: *mut LeanObject,
    mut v_a_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u8 = 0;
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4487_ = lean_ctor_get(v_a_4486_, 0);
                v_idx_4488_ = lean_ctor_get(v_a_4486_, 1);
                v___x_4489_ = lean_byte_array_size(v_array_4487_);
                v___x_4490_ = lean_nat_dec_lt(v_idx_4488_, v___x_4489_);
                if v___x_4490_ == 0 {
                    lean_dec_ref(v_acc_4485_);
                    v___x_4491_ = lean_box(0);
                    v___x_4492_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4492_, 0, v_a_4486_);
                    lean_ctor_set(v___x_4492_, 1, v___x_4491_);
                    return v___x_4492_;
                } else {
                    v___x_4493_ = lean_byte_array_fget(v_array_4487_, v_idx_4488_);
                    v___x_4494_ = 0;
                    v___x_4495_ = lean_uint8_dec_eq(v___x_4493_, v___x_4494_);
                    if v___x_4495_ == 0 {
                        v___x_4496_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4486_);
                        if lean_obj_tag(v___x_4496_) == 0 {
                            v_pos_4497_ = lean_ctor_get(v___x_4496_, 0);
                            lean_inc(v_pos_4497_);
                            v_res_4498_ = lean_ctor_get(v___x_4496_, 1);
                            lean_inc(v_res_4498_);
                            lean_dec_ref_known(v___x_4496_, 2);
                            v___x_4499_ = lean_array_push(v_acc_4485_, v_res_4498_);
                            v_acc_4485_ = v___x_4499_;
                            v_a_4486_ = v_pos_4497_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_acc_4485_);
                            v_pos_4501_ = lean_ctor_get(v___x_4496_, 0);
                            v_err_4502_ = lean_ctor_get(v___x_4496_, 1);
                            v_isSharedCheck_4509_ = (!lean_is_exclusive(v___x_4496_)) as u8;
                            if v_isSharedCheck_4509_ == 0 {
                                v___x_4504_ = v___x_4496_;
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_err_4502_);
                                lean_inc(v_pos_4501_);
                                lean_dec(v___x_4496_);
                                v___x_4504_ = lean_box(0);
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_4510_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4510_, 0, v_a_4486_);
                        lean_ctor_set(v___x_4510_, 1, v_acc_4485_);
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
                    v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_pos_4501_);
                    lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_err_4502_);
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
    mut v_a_4511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    v___x_4512_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0;
    v___x_4513_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_4512_, v_a_4511_);
    return v___x_4513_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(
    mut v_acc_4514_: *mut LeanObject,
    mut v_a_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4516_ = lean_ctor_get(v_a_4515_, 0);
                v_idx_4517_ = lean_ctor_get(v_a_4515_, 1);
                v___x_4518_ = lean_byte_array_size(v_array_4516_);
                v___x_4519_ = lean_nat_dec_lt(v_idx_4517_, v___x_4518_);
                if v___x_4519_ == 0 {
                    lean_dec_ref(v_acc_4514_);
                    v___x_4520_ = lean_box(0);
                    v___x_4521_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4521_, 0, v_a_4515_);
                    lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                    return v___x_4521_;
                } else {
                    v___x_4522_ = lean_byte_array_fget(v_array_4516_, v_idx_4517_);
                    v___x_4523_ = 0;
                    v___x_4524_ = lean_uint8_dec_eq(v___x_4522_, v___x_4523_);
                    if v___x_4524_ == 0 {
                        v___x_4525_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_4515_);
                        if lean_obj_tag(v___x_4525_) == 0 {
                            v_pos_4526_ = lean_ctor_get(v___x_4525_, 0);
                            lean_inc(v_pos_4526_);
                            v_res_4527_ = lean_ctor_get(v___x_4525_, 1);
                            lean_inc(v_res_4527_);
                            lean_dec_ref_known(v___x_4525_, 2);
                            v___x_4528_ = lean_array_push(v_acc_4514_, v_res_4527_);
                            v_acc_4514_ = v___x_4528_;
                            v_a_4515_ = v_pos_4526_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_acc_4514_);
                            v_pos_4530_ = lean_ctor_get(v___x_4525_, 0);
                            v_err_4531_ = lean_ctor_get(v___x_4525_, 1);
                            v_isSharedCheck_4538_ = (!lean_is_exclusive(v___x_4525_)) as u8;
                            if v_isSharedCheck_4538_ == 0 {
                                v___x_4533_ = v___x_4525_;
                                v_isShared_4534_ = v_isSharedCheck_4538_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_err_4531_);
                                lean_inc(v_pos_4530_);
                                lean_dec(v___x_4525_);
                                v___x_4533_ = lean_box(0);
                                v_isShared_4534_ = v_isSharedCheck_4538_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_4539_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4539_, 0, v_a_4515_);
                        lean_ctor_set(v___x_4539_, 1, v_acc_4514_);
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
                    v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_pos_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_err_4531_);
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
    mut v_a_4540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    v___x_4541_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0;
    v___x_4542_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_4541_, v_a_4540_);
    return v___x_4542_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(
    mut v_a_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v_array_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: u8 = 0;
    let mut v_got_4572_: u8 = 0;
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v_array_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: u8 = 0;
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_got_4602_: u8 = 0;
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4639_: u8 = 0;
    let mut v_unused_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_pos_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v_pos_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v_reuseFailAlloc_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_unused_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4665_: u8 = 0;
    let mut v_pos_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4674_: u8 = 0;
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut v_pos_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4680_: u8 = 0;
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4544_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_4543_);
                if lean_obj_tag(v___x_4544_) == 0 {
                    v_pos_4545_ = lean_ctor_get(v___x_4544_, 0);
                    v_res_4546_ = lean_ctor_get(v___x_4544_, 1);
                    v_isSharedCheck_4675_ = (!lean_is_exclusive(v___x_4544_)) as u8;
                    if v_isSharedCheck_4675_ == 0 {
                        v___x_4548_ = v___x_4544_;
                        v_isShared_4549_ = v_isSharedCheck_4675_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4546_);
                        lean_inc(v_pos_4545_);
                        lean_dec(v___x_4544_);
                        v___x_4548_ = lean_box(0);
                        v_isShared_4549_ = v_isSharedCheck_4675_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4676_ = lean_ctor_get(v___x_4544_, 0);
                    v_err_4677_ = lean_ctor_get(v___x_4544_, 1);
                    v_isSharedCheck_4684_ = (!lean_is_exclusive(v___x_4544_)) as u8;
                    if v_isSharedCheck_4684_ == 0 {
                        v___x_4679_ = v___x_4544_;
                        v_isShared_4680_ = v_isSharedCheck_4684_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_err_4677_);
                        lean_inc(v_pos_4676_);
                        lean_dec(v___x_4544_);
                        v___x_4679_ = lean_box(0);
                        v_isShared_4680_ = v_isSharedCheck_4684_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4550_ = lean_unsigned_to_nat(0);
                v___x_4551_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_4552_ = lean_int_dec_lt(v___x_4551_, v_res_4546_);
                if v___x_4552_ == 0 {
                    lean_dec(v_res_4546_);
                    v___x_4553_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
                    if v_isShared_4549_ == 0 {
                        lean_ctor_set_tag(v___x_4548_, 1);
                        lean_ctor_set(v___x_4548_, 1, v___x_4553_);
                        v___x_4555_ = v___x_4548_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_pos_4545_);
                        lean_ctor_set(v_reuseFailAlloc_4556_, 1, v___x_4553_);
                        v___x_4555_ = v_reuseFailAlloc_4556_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4548_);
                    v___x_4557_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_4545_);
                    if lean_obj_tag(v___x_4557_) == 0 {
                        v_pos_4558_ = lean_ctor_get(v___x_4557_, 0);
                        v_res_4559_ = lean_ctor_get(v___x_4557_, 1);
                        v_isSharedCheck_4665_ = (!lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4665_ == 0 {
                            v___x_4561_ = v___x_4557_;
                            v_isShared_4562_ = v_isSharedCheck_4665_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_res_4559_);
                            lean_inc(v_pos_4558_);
                            lean_dec(v___x_4557_);
                            v___x_4561_ = lean_box(0);
                            v_isShared_4562_ = v_isSharedCheck_4665_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_4546_);
                        v_pos_4666_ = lean_ctor_get(v___x_4557_, 0);
                        v_err_4667_ = lean_ctor_get(v___x_4557_, 1);
                        v_isSharedCheck_4674_ = (!lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4674_ == 0 {
                            v___x_4669_ = v___x_4557_;
                            v_isShared_4670_ = v_isSharedCheck_4674_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_err_4667_);
                            lean_inc(v_pos_4666_);
                            lean_dec(v___x_4557_);
                            v___x_4669_ = lean_box(0);
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
                v_array_4563_ = lean_ctor_get(v_pos_4558_, 0);
                v_idx_4564_ = lean_ctor_get(v_pos_4558_, 1);
                v___x_4565_ = lean_byte_array_size(v_array_4563_);
                v___x_4566_ = lean_nat_dec_lt(v_idx_4564_, v___x_4565_);
                if v___x_4566_ == 0 {
                    lean_dec(v_res_4559_);
                    lean_dec(v_res_4546_);
                    v___x_4567_ = lean_box(0);
                    if v_isShared_4562_ == 0 {
                        lean_ctor_set_tag(v___x_4561_, 1);
                        lean_ctor_set(v___x_4561_, 1, v___x_4567_);
                        v___x_4569_ = v___x_4561_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_pos_4558_);
                        lean_ctor_set(v_reuseFailAlloc_4570_, 1, v___x_4567_);
                        v___x_4569_ = v_reuseFailAlloc_4570_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4571_ = 0;
                    v_got_4572_ = lean_byte_array_fget(v_array_4563_, v_idx_4564_);
                    v___x_4573_ = lean_uint8_dec_eq(v_got_4572_, v___x_4571_);
                    if v___x_4573_ == 0 {
                        lean_dec(v_res_4559_);
                        lean_dec(v_res_4546_);
                        v___x_4574_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        if v_isShared_4562_ == 0 {
                            lean_ctor_set_tag(v___x_4561_, 1);
                            lean_ctor_set(v___x_4561_, 1, v___x_4574_);
                            v___x_4576_ = v___x_4561_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_pos_4558_);
                            lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4574_);
                            v___x_4576_ = v_reuseFailAlloc_4577_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_4564_);
                        lean_inc_ref(v_array_4563_);
                        lean_del_object(v___x_4561_);
                        v_isSharedCheck_4662_ = (!lean_is_exclusive(v_pos_4558_)) as u8;
                        if v_isSharedCheck_4662_ == 0 {
                            v_unused_4663_ = lean_ctor_get(v_pos_4558_, 1);
                            lean_dec(v_unused_4663_);
                            v_unused_4664_ = lean_ctor_get(v_pos_4558_, 0);
                            lean_dec(v_unused_4664_);
                            v___x_4579_ = v_pos_4558_;
                            v_isShared_4580_ = v_isSharedCheck_4662_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_pos_4558_);
                            v___x_4579_ = lean_box(0);
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
                v___x_4581_ = lean_unsigned_to_nat(1);
                v___x_4582_ = lean_nat_add(v_idx_4564_, v___x_4581_);
                lean_dec(v_idx_4564_);
                if v_isShared_4580_ == 0 {
                    lean_ctor_set(v___x_4579_, 1, v___x_4582_);
                    v___x_4584_ = v___x_4579_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_array_4563_);
                    lean_ctor_set(v_reuseFailAlloc_4661_, 1, v___x_4582_);
                    v___x_4584_ = v_reuseFailAlloc_4661_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4585_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_4584_);
                if lean_obj_tag(v___x_4585_) == 0 {
                    v_pos_4586_ = lean_ctor_get(v___x_4585_, 0);
                    lean_inc(v_pos_4586_);
                    v_res_4587_ = lean_ctor_get(v___x_4585_, 1);
                    lean_inc(v_res_4587_);
                    lean_dec_ref_known(v___x_4585_, 2);
                    v___x_4588_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_4586_);
                    if lean_obj_tag(v___x_4588_) == 0 {
                        v_pos_4589_ = lean_ctor_get(v___x_4588_, 0);
                        v_res_4590_ = lean_ctor_get(v___x_4588_, 1);
                        v_isSharedCheck_4642_ = (!lean_is_exclusive(v___x_4588_)) as u8;
                        if v_isSharedCheck_4642_ == 0 {
                            v___x_4592_ = v___x_4588_;
                            v_isShared_4593_ = v_isSharedCheck_4642_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_res_4590_);
                            lean_inc(v_pos_4589_);
                            lean_dec(v___x_4588_);
                            v___x_4592_ = lean_box(0);
                            v_isShared_4593_ = v_isSharedCheck_4642_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_4587_);
                        lean_dec(v_res_4559_);
                        lean_dec(v_res_4546_);
                        v_pos_4643_ = lean_ctor_get(v___x_4588_, 0);
                        v_err_4644_ = lean_ctor_get(v___x_4588_, 1);
                        v_isSharedCheck_4651_ = (!lean_is_exclusive(v___x_4588_)) as u8;
                        if v_isSharedCheck_4651_ == 0 {
                            v___x_4646_ = v___x_4588_;
                            v_isShared_4647_ = v_isSharedCheck_4651_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_err_4644_);
                            lean_inc(v_pos_4643_);
                            lean_dec(v___x_4588_);
                            v___x_4646_ = lean_box(0);
                            v_isShared_4647_ = v_isSharedCheck_4651_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_res_4559_);
                    lean_dec(v_res_4546_);
                    v_pos_4652_ = lean_ctor_get(v___x_4585_, 0);
                    v_err_4653_ = lean_ctor_get(v___x_4585_, 1);
                    v_isSharedCheck_4660_ = (!lean_is_exclusive(v___x_4585_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4655_ = v___x_4585_;
                        v_isShared_4656_ = v_isSharedCheck_4660_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_err_4653_);
                        lean_inc(v_pos_4652_);
                        lean_dec(v___x_4585_);
                        v___x_4655_ = lean_box(0);
                        v_isShared_4656_ = v_isSharedCheck_4660_;
                        state = 19;
                        continue;
                    }
                }
            }
            8 => {
                v_array_4594_ = lean_ctor_get(v_pos_4589_, 0);
                v_idx_4595_ = lean_ctor_get(v_pos_4589_, 1);
                v___x_4596_ = lean_byte_array_size(v_array_4594_);
                v___x_4597_ = lean_nat_dec_lt(v_idx_4595_, v___x_4596_);
                if v___x_4597_ == 0 {
                    lean_dec(v_res_4590_);
                    lean_dec(v_res_4587_);
                    lean_dec(v_res_4559_);
                    lean_dec(v_res_4546_);
                    v___x_4598_ = lean_box(0);
                    if v_isShared_4593_ == 0 {
                        lean_ctor_set_tag(v___x_4592_, 1);
                        lean_ctor_set(v___x_4592_, 1, v___x_4598_);
                        v___x_4600_ = v___x_4592_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_pos_4589_);
                        lean_ctor_set(v_reuseFailAlloc_4601_, 1, v___x_4598_);
                        v___x_4600_ = v_reuseFailAlloc_4601_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_got_4602_ = lean_byte_array_fget(v_array_4594_, v_idx_4595_);
                    v___x_4603_ = lean_uint8_dec_eq(v_got_4602_, v___x_4571_);
                    if v___x_4603_ == 0 {
                        lean_dec(v_res_4590_);
                        lean_dec(v_res_4587_);
                        lean_dec(v_res_4559_);
                        lean_dec(v_res_4546_);
                        v___x_4604_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        if v_isShared_4593_ == 0 {
                            lean_ctor_set_tag(v___x_4592_, 1);
                            lean_ctor_set(v___x_4592_, 1, v___x_4604_);
                            v___x_4606_ = v___x_4592_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_pos_4589_);
                            lean_ctor_set(v_reuseFailAlloc_4607_, 1, v___x_4604_);
                            v___x_4606_ = v_reuseFailAlloc_4607_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_4595_);
                        lean_inc_ref(v_array_4594_);
                        v_isSharedCheck_4639_ = (!lean_is_exclusive(v_pos_4589_)) as u8;
                        if v_isSharedCheck_4639_ == 0 {
                            v_unused_4640_ = lean_ctor_get(v_pos_4589_, 1);
                            lean_dec(v_unused_4640_);
                            v_unused_4641_ = lean_ctor_get(v_pos_4589_, 0);
                            lean_dec(v_unused_4641_);
                            v___x_4609_ = v_pos_4589_;
                            v_isShared_4610_ = v_isSharedCheck_4639_;
                            state = 11;
                            continue;
                        } else {
                            lean_dec(v_pos_4589_);
                            v___x_4609_ = lean_box(0);
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
                lean_dec(v_res_4546_);
                v___x_4612_ = lean_nat_add(v_idx_4595_, v___x_4581_);
                lean_dec(v_idx_4595_);
                if v_isShared_4610_ == 0 {
                    lean_ctor_set(v___x_4609_, 1, v___x_4612_);
                    v___x_4614_ = v___x_4609_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_array_4594_);
                    lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4612_);
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
                        v___x_4620_ = lean_alloc_ctor(2, 5, (0) as u32);
                        lean_ctor_set(v___x_4620_, 0, v___x_4611_);
                        lean_ctor_set(v___x_4620_, 1, v_res_4559_);
                        lean_ctor_set(v___x_4620_, 2, v___x_4619_);
                        lean_ctor_set(v___x_4620_, 3, v_res_4587_);
                        lean_ctor_set(v___x_4620_, 4, v_res_4590_);
                        if v_isShared_4593_ == 0 {
                            lean_ctor_set(v___x_4592_, 1, v___x_4620_);
                            lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4622_ = v___x_4592_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4614_);
                            lean_ctor_set(v_reuseFailAlloc_4623_, 1, v___x_4620_);
                            v___x_4622_ = v_reuseFailAlloc_4623_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_4590_);
                        v___x_4624_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_4624_, 0, v___x_4611_);
                        lean_ctor_set(v___x_4624_, 1, v_res_4559_);
                        lean_ctor_set(v___x_4624_, 2, v_res_4587_);
                        if v_isShared_4593_ == 0 {
                            lean_ctor_set(v___x_4592_, 1, v___x_4624_);
                            lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4626_ = v___x_4592_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4614_);
                            lean_ctor_set(v_reuseFailAlloc_4627_, 1, v___x_4624_);
                            v___x_4626_ = v_reuseFailAlloc_4627_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_res_4559_);
                    v___x_4628_ = lean_array_get_size(v_res_4590_);
                    lean_dec(v_res_4590_);
                    v___x_4629_ = lean_nat_dec_eq(v___x_4628_, v___x_4550_);
                    if v___x_4629_ == 0 {
                        lean_dec(v___x_4611_);
                        lean_dec(v_res_4587_);
                        v___x_4630_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2;
                        if v_isShared_4593_ == 0 {
                            lean_ctor_set_tag(v___x_4592_, 1);
                            lean_ctor_set(v___x_4592_, 1, v___x_4630_);
                            lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4632_ = v___x_4592_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4614_);
                            lean_ctor_set(v_reuseFailAlloc_4633_, 1, v___x_4630_);
                            v___x_4632_ = v_reuseFailAlloc_4633_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_4634_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4634_, 0, v___x_4611_);
                        lean_ctor_set(v___x_4634_, 1, v_res_4587_);
                        if v_isShared_4593_ == 0 {
                            lean_ctor_set(v___x_4592_, 1, v___x_4634_);
                            lean_ctor_set(v___x_4592_, 0, v___x_4614_);
                            v___x_4636_ = v___x_4592_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4614_);
                            lean_ctor_set(v_reuseFailAlloc_4637_, 1, v___x_4634_);
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
                    v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_pos_4643_);
                    lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_err_4644_);
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
                    v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_pos_4652_);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_err_4653_);
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
                    v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_pos_4666_);
                    lean_ctor_set(v_reuseFailAlloc_4673_, 1, v_err_4667_);
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
                    v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_pos_4676_);
                    lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_err_4677_);
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
    mut v_a_4685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v_array_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: u8 = 0;
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut v_got_4701_: u8 = 0;
    let mut v___x_4702_: u8 = 0;
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut v_unused_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4722_: u8 = 0;
    let mut v_pos_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_4685_);
                if lean_obj_tag(v___x_4686_) == 0 {
                    v_pos_4687_ = lean_ctor_get(v___x_4686_, 0);
                    v_res_4688_ = lean_ctor_get(v___x_4686_, 1);
                    v_isSharedCheck_4722_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4722_ == 0 {
                        v___x_4690_ = v___x_4686_;
                        v_isShared_4691_ = v_isSharedCheck_4722_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4688_);
                        lean_inc(v_pos_4687_);
                        lean_dec(v___x_4686_);
                        v___x_4690_ = lean_box(0);
                        v_isShared_4691_ = v_isSharedCheck_4722_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4723_ = lean_ctor_get(v___x_4686_, 0);
                    v_err_4724_ = lean_ctor_get(v___x_4686_, 1);
                    v_isSharedCheck_4731_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4731_ == 0 {
                        v___x_4726_ = v___x_4686_;
                        v_isShared_4727_ = v_isSharedCheck_4731_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_err_4724_);
                        lean_inc(v_pos_4723_);
                        lean_dec(v___x_4686_);
                        v___x_4726_ = lean_box(0);
                        v_isShared_4727_ = v_isSharedCheck_4731_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_array_4692_ = lean_ctor_get(v_pos_4687_, 0);
                v_idx_4693_ = lean_ctor_get(v_pos_4687_, 1);
                v___x_4694_ = lean_byte_array_size(v_array_4692_);
                v___x_4695_ = lean_nat_dec_lt(v_idx_4693_, v___x_4694_);
                if v___x_4695_ == 0 {
                    lean_dec(v_res_4688_);
                    v___x_4696_ = lean_box(0);
                    if v_isShared_4691_ == 0 {
                        lean_ctor_set_tag(v___x_4690_, 1);
                        lean_ctor_set(v___x_4690_, 1, v___x_4696_);
                        v___x_4698_ = v___x_4690_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_pos_4687_);
                        lean_ctor_set(v_reuseFailAlloc_4699_, 1, v___x_4696_);
                        v___x_4698_ = v_reuseFailAlloc_4699_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4700_ = 0;
                    v_got_4701_ = lean_byte_array_fget(v_array_4692_, v_idx_4693_);
                    v___x_4702_ = lean_uint8_dec_eq(v_got_4701_, v___x_4700_);
                    if v___x_4702_ == 0 {
                        lean_dec(v_res_4688_);
                        v___x_4703_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3,
                        );
                        if v_isShared_4691_ == 0 {
                            lean_ctor_set_tag(v___x_4690_, 1);
                            lean_ctor_set(v___x_4690_, 1, v___x_4703_);
                            v___x_4705_ = v___x_4690_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_pos_4687_);
                            lean_ctor_set(v_reuseFailAlloc_4706_, 1, v___x_4703_);
                            v___x_4705_ = v_reuseFailAlloc_4706_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_inc(v_idx_4693_);
                        lean_inc_ref(v_array_4692_);
                        v_isSharedCheck_4719_ = (!lean_is_exclusive(v_pos_4687_)) as u8;
                        if v_isSharedCheck_4719_ == 0 {
                            v_unused_4720_ = lean_ctor_get(v_pos_4687_, 1);
                            lean_dec(v_unused_4720_);
                            v_unused_4721_ = lean_ctor_get(v_pos_4687_, 0);
                            lean_dec(v_unused_4721_);
                            v___x_4708_ = v_pos_4687_;
                            v_isShared_4709_ = v_isSharedCheck_4719_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_pos_4687_);
                            v___x_4708_ = lean_box(0);
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
                v___x_4710_ = lean_unsigned_to_nat(1);
                v___x_4711_ = lean_nat_add(v_idx_4693_, v___x_4710_);
                lean_dec(v_idx_4693_);
                if v_isShared_4709_ == 0 {
                    lean_ctor_set(v___x_4708_, 1, v___x_4711_);
                    v___x_4713_ = v___x_4708_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_array_4692_);
                    lean_ctor_set(v_reuseFailAlloc_4718_, 1, v___x_4711_);
                    v___x_4713_ = v_reuseFailAlloc_4718_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4714_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4714_, 0, v_res_4688_);
                if v_isShared_4691_ == 0 {
                    lean_ctor_set(v___x_4690_, 1, v___x_4714_);
                    lean_ctor_set(v___x_4690_, 0, v___x_4713_);
                    v___x_4716_ = v___x_4690_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4713_);
                    lean_ctor_set(v_reuseFailAlloc_4717_, 1, v___x_4714_);
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
                    v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_pos_4723_);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_err_4724_);
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
    mut v_a_4735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v_c_4745_: u8 = 0;
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: u8 = 0;
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: u8 = 0;
    let mut v___x_4753_: u8 = 0;
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_unused_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4736_ = lean_ctor_get(v_a_4735_, 0);
                v_idx_4737_ = lean_ctor_get(v_a_4735_, 1);
                v___x_4738_ = lean_byte_array_size(v_array_4736_);
                v___x_4739_ = lean_nat_dec_lt(v_idx_4737_, v___x_4738_);
                if v___x_4739_ == 0 {
                    v___x_4740_ = lean_box(0);
                    v___x_4741_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4741_, 0, v_a_4735_);
                    lean_ctor_set(v___x_4741_, 1, v___x_4740_);
                    return v___x_4741_;
                } else {
                    lean_inc(v_idx_4737_);
                    lean_inc_ref(v_array_4736_);
                    v_isSharedCheck_4763_ = (!lean_is_exclusive(v_a_4735_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v_unused_4764_ = lean_ctor_get(v_a_4735_, 1);
                        lean_dec(v_unused_4764_);
                        v_unused_4765_ = lean_ctor_get(v_a_4735_, 0);
                        lean_dec(v_unused_4765_);
                        v___x_4743_ = v_a_4735_;
                        v_isShared_4744_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_4735_);
                        v___x_4743_ = lean_box(0);
                        v_isShared_4744_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_c_4745_ = lean_byte_array_fget(v_array_4736_, v_idx_4737_);
                v___x_4746_ = lean_unsigned_to_nat(1);
                v___x_4747_ = lean_nat_add(v_idx_4737_, v___x_4746_);
                lean_dec(v_idx_4737_);
                if v_isShared_4744_ == 0 {
                    lean_ctor_set(v___x_4743_, 1, v___x_4747_);
                    v_it_x27_4749_ = v___x_4743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_array_4736_);
                    lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4747_);
                    v_it_x27_4749_ = v_reuseFailAlloc_4762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4750_ = lean_uint8_once(
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
                    v___x_4752_ = lean_uint8_once(
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
                        lean_dec_ref(v___x_4756_);
                        v___x_4758_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4758_, 0, v___x_4757_);
                        v___x_4759_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_4759_, 0, v_it_x27_4749_);
                        lean_ctor_set(v___x_4759_, 1, v___x_4758_);
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
    mut v_acc_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v_idx_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: u8 = 0;
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_4767_);
                v___x_4768_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_4767_);
                if lean_obj_tag(v___x_4768_) == 0 {
                    lean_dec_ref(v_a_4767_);
                    v_pos_4769_ = lean_ctor_get(v___x_4768_, 0);
                    lean_inc(v_pos_4769_);
                    v_res_4770_ = lean_ctor_get(v___x_4768_, 1);
                    lean_inc(v_res_4770_);
                    lean_dec_ref_known(v___x_4768_, 2);
                    v___x_4771_ = lean_array_push(v_acc_4766_, v_res_4770_);
                    v_acc_4766_ = v___x_4771_;
                    v_a_4767_ = v_pos_4769_;
                    state = 0;
                    continue;
                } else {
                    v_pos_4773_ = lean_ctor_get(v___x_4768_, 0);
                    v_err_4774_ = lean_ctor_get(v___x_4768_, 1);
                    v_isSharedCheck_4787_ = (!lean_is_exclusive(v___x_4768_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v___x_4776_ = v___x_4768_;
                        v_isShared_4777_ = v_isSharedCheck_4787_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_err_4774_);
                        lean_inc(v_pos_4773_);
                        lean_dec(v___x_4768_);
                        v___x_4776_ = lean_box(0);
                        v_isShared_4777_ = v_isSharedCheck_4787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_idx_4778_ = lean_ctor_get(v_a_4767_, 1);
                lean_inc(v_idx_4778_);
                lean_dec_ref(v_a_4767_);
                v_idx_4779_ = lean_ctor_get(v_pos_4773_, 1);
                v___x_4780_ = lean_nat_dec_eq(v_idx_4778_, v_idx_4779_);
                lean_dec(v_idx_4778_);
                if v___x_4780_ == 0 {
                    lean_dec_ref(v_acc_4766_);
                    if v_isShared_4777_ == 0 {
                        v___x_4782_ = v___x_4776_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_pos_4773_);
                        lean_ctor_set(v_reuseFailAlloc_4783_, 1, v_err_4774_);
                        v___x_4782_ = v_reuseFailAlloc_4783_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_err_4774_);
                    if v_isShared_4777_ == 0 {
                        lean_ctor_set_tag(v___x_4776_, 0);
                        lean_ctor_set(v___x_4776_, 1, v_acc_4766_);
                        v___x_4785_ = v___x_4776_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_pos_4773_);
                        lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_acc_4766_);
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
    mut v_a_4791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: u8 = 0;
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_unused_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4792_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0;
                v___x_4793_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_4792_, v_a_4791_);
                if lean_obj_tag(v___x_4793_) == 0 {
                    v_pos_4794_ = lean_ctor_get(v___x_4793_, 0);
                    lean_inc(v_pos_4794_);
                    v_array_4795_ = lean_ctor_get(v_pos_4794_, 0);
                    v_idx_4796_ = lean_ctor_get(v_pos_4794_, 1);
                    v___x_4797_ = lean_byte_array_size(v_array_4795_);
                    v___x_4798_ = lean_nat_dec_lt(v_idx_4796_, v___x_4797_);
                    if v___x_4798_ == 0 {
                        lean_dec(v_pos_4794_);
                        return v___x_4793_;
                    } else {
                        v_isSharedCheck_4806_ = (!lean_is_exclusive(v___x_4793_)) as u8;
                        if v_isSharedCheck_4806_ == 0 {
                            v_unused_4807_ = lean_ctor_get(v___x_4793_, 1);
                            lean_dec(v_unused_4807_);
                            v_unused_4808_ = lean_ctor_get(v___x_4793_, 0);
                            lean_dec(v_unused_4808_);
                            v___x_4800_ = v___x_4793_;
                            v_isShared_4801_ = v_isSharedCheck_4806_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4793_);
                            v___x_4800_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_4800_, 1);
                    lean_ctor_set(v___x_4800_, 1, v___x_4802_);
                    v___x_4804_ = v___x_4800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_pos_4794_);
                    lean_ctor_set(v_reuseFailAlloc_4805_, 1, v___x_4802_);
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
    mut v_a_4809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4811_: u8 = 0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: u8 = 0;
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v___x_4821_: u8 = 0;
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4814_ = lean_ctor_get(v_a_4809_, 0);
                v_idx_4815_ = lean_ctor_get(v_a_4809_, 1);
                v___x_4816_ = lean_byte_array_size(v_array_4814_);
                v___x_4817_ = lean_nat_dec_lt(v_idx_4815_, v___x_4816_);
                if v___x_4817_ == 0 {
                    v___x_4818_ = lean_box(0);
                    v___x_4819_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4819_, 0, v_a_4809_);
                    lean_ctor_set(v___x_4819_, 1, v___x_4818_);
                    return v___x_4819_;
                } else {
                    v___x_4820_ = lean_byte_array_fget(v_array_4814_, v_idx_4815_);
                    v___x_4821_ = lean_uint8_once(
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
                        v___x_4823_ = lean_uint8_once(
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
    mut v_path_4825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4831_: u8 = 0;
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4844_: u8 = 0;
    let mut v_a_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4827_ = l_IO_FS_readBinFile(v_path_4825_);
                if lean_obj_tag(v___x_4827_) == 0 {
                    v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
                    v_isSharedCheck_4849_ = (!lean_is_exclusive(v___x_4827_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4830_ = v___x_4827_;
                        v_isShared_4831_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4828_);
                        lean_dec(v___x_4827_);
                        v___x_4830_ = lean_box(0);
                        v_isShared_4831_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4850_ = lean_ctor_get(v___x_4827_, 0);
                    v_isSharedCheck_4857_ = (!lean_is_exclusive(v___x_4827_)) as u8;
                    if v_isSharedCheck_4857_ == 0 {
                        v___x_4852_ = v___x_4827_;
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4850_);
                        lean_dec(v___x_4827_);
                        v___x_4852_ = lean_box(0);
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4832_ = lean_alloc_closure(
                    l_Std_Tactic_BVDecide_LRAT_Parser_parseActions as *mut core::ffi::c_void,
                    1,
                    0,
                );
                v___x_4833_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_4832_, v_a_4828_);
                if lean_obj_tag(v___x_4833_) == 0 {
                    v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4844_ = (!lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4844_ == 0 {
                        v___x_4836_ = v___x_4833_;
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4834_);
                        lean_dec(v___x_4833_);
                        v___x_4836_ = lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4845_ = lean_ctor_get(v___x_4833_, 0);
                    lean_inc(v_a_4845_);
                    lean_dec_ref_known(v___x_4833_, 1);
                    if v_isShared_4831_ == 0 {
                        lean_ctor_set(v___x_4830_, 0, v_a_4845_);
                        v___x_4847_ = v___x_4830_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4845_);
                        v___x_4847_ = v_reuseFailAlloc_4848_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4837_ == 0 {
                    lean_ctor_set_tag(v___x_4836_, 18);
                    v___x_4839_ = v___x_4836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4843_ = lean_alloc_ctor(18, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4834_);
                    v___x_4839_ = v_reuseFailAlloc_4843_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4831_ == 0 {
                    lean_ctor_set_tag(v___x_4830_, 1);
                    lean_ctor_set(v___x_4830_, 0, v___x_4839_);
                    v___x_4841_ = v___x_4830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4839_);
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
                    v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
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
    mut v_path_4858_: *mut LeanObject,
    mut v_a_4859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4860_: *mut LeanObject = core::ptr::null_mut();
    v_res_4860_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_4858_);
    lean_dec_ref(v_path_4858_);
    return v_res_4860_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_parseLRATProof(
    mut v_proof_4861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    v___x_4862_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Parser_parseActions as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4863_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_4862_, v_proof_4861_);
    return v___x_4863_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(
    mut v_as_4865_: *mut LeanObject,
    mut v_i_4866_: usize,
    mut v_stop_4867_: usize,
    mut v_b_4868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: usize = 0;
    let mut v___x_4876_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4869_ = lean_usize_dec_eq(v_i_4866_, v_stop_4867_);
                if v___x_4869_ == 0 {
                    v___x_4870_ = lean_array_uget_borrowed(v_as_4865_, v_i_4866_);
                    lean_inc(v___x_4870_);
                    v___x_4871_ = l_Nat_reprFast(v___x_4870_);
                    v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
                    v___x_4873_ = lean_string_append(v___x_4871_, v___x_4872_);
                    v___x_4874_ = lean_string_append(v_b_4868_, v___x_4873_);
                    lean_dec_ref(v___x_4873_);
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
    mut v_as_4878_: *mut LeanObject,
    mut v_i_4879_: *mut LeanObject,
    mut v_stop_4880_: *mut LeanObject,
    mut v_b_4881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4882_: usize = 0;
    let mut v_stop_boxed_4883_: usize = 0;
    let mut v_res_4884_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4882_ = lean_unbox_usize(v_i_4879_);
    lean_dec(v_i_4879_);
    v_stop_boxed_4883_ = lean_unbox_usize(v_stop_4880_);
    lean_dec(v_stop_4880_);
    v_res_4884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_4878_, v_i_boxed_4882_, v_stop_boxed_4883_, v_b_4881_);
    lean_dec_ref(v_as_4878_);
    return v_res_4884_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(
    mut v_ids_4886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: u8 = 0;
    v___x_4887_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_4888_ = lean_unsigned_to_nat(0);
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
                let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
                v___x_4892_ = 0usize;
                v___x_4893_ = lean_usize_of_nat(v___x_4889_);
                v___x_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_4886_, v___x_4892_, v___x_4893_, v___x_4887_);
                return v___x_4894_;
            }
        } else {
            let mut v___x_4895_: usize = 0;
            let mut v___x_4896_: usize = 0;
            let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
            v___x_4895_ = 0usize;
            v___x_4896_ = lean_usize_of_nat(v___x_4889_);
            v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_4886_, v___x_4895_, v___x_4896_, v___x_4887_);
            return v___x_4897_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(
    mut v_ids_4898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4899_: *mut LeanObject = core::ptr::null_mut();
    v_res_4899_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_4898_);
    lean_dec_ref(v_ids_4898_);
    return v_res_4899_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(
    mut v_hint_4901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4902_ = lean_ctor_get(v_hint_4901_, 0);
    lean_inc(v_fst_4902_);
    v_snd_4903_ = lean_ctor_get(v_hint_4901_, 1);
    lean_inc(v_snd_4903_);
    lean_dec_ref(v_hint_4901_);
    v___x_4904_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0;
    v___x_4905_ = l_Nat_reprFast(v_fst_4902_);
    v___x_4906_ = lean_string_append(v___x_4904_, v___x_4905_);
    lean_dec_ref(v___x_4905_);
    v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
    v___x_4908_ = lean_string_append(v___x_4906_, v___x_4907_);
    v___x_4909_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_4903_);
    lean_dec(v_snd_4903_);
    v___x_4910_ = lean_string_append(v___x_4908_, v___x_4909_);
    lean_dec_ref(v___x_4909_);
    return v___x_4910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(
    mut v_as_4911_: *mut LeanObject,
    mut v_i_4912_: usize,
    mut v_stop_4913_: usize,
    mut v_b_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4915_: u8 = 0;
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4915_ = lean_usize_dec_eq(v_i_4912_, v_stop_4913_);
                if v___x_4915_ == 0 {
                    v___x_4916_ = lean_array_uget_borrowed(v_as_4911_, v_i_4912_);
                    lean_inc(v___x_4916_);
                    v___x_4917_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_4916_);
                    v___x_4918_ = lean_string_append(v_b_4914_, v___x_4917_);
                    lean_dec_ref(v___x_4917_);
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
    mut v_as_4922_: *mut LeanObject,
    mut v_i_4923_: *mut LeanObject,
    mut v_stop_4924_: *mut LeanObject,
    mut v_b_4925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4926_: usize = 0;
    let mut v_stop_boxed_4927_: usize = 0;
    let mut v_res_4928_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4926_ = lean_unbox_usize(v_i_4923_);
    lean_dec(v_i_4923_);
    v_stop_boxed_4927_ = lean_unbox_usize(v_stop_4924_);
    lean_dec(v_stop_4924_);
    v_res_4928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_4922_, v_i_boxed_4926_, v_stop_boxed_4927_, v_b_4925_);
    lean_dec_ref(v_as_4922_);
    return v_res_4928_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(
    mut v_hints_4929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: u8 = 0;
    v___x_4930_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_4931_ = lean_unsigned_to_nat(0);
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
                let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
                v___x_4935_ = 0usize;
                v___x_4936_ = lean_usize_of_nat(v___x_4932_);
                v___x_4937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_4929_, v___x_4935_, v___x_4936_, v___x_4930_);
                return v___x_4937_;
            }
        } else {
            let mut v___x_4938_: usize = 0;
            let mut v___x_4939_: usize = 0;
            let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
            v___x_4938_ = 0usize;
            v___x_4939_ = lean_usize_of_nat(v___x_4932_);
            v___x_4940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_4929_, v___x_4938_, v___x_4939_, v___x_4930_);
            return v___x_4940_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(
    mut v_hints_4941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4942_: *mut LeanObject = core::ptr::null_mut();
    v_res_4942_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_4941_);
    lean_dec_ref(v_hints_4941_);
    return v_res_4942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(
    mut v_as_4943_: *mut LeanObject,
    mut v_i_4944_: usize,
    mut v_stop_4945_: usize,
    mut v_b_4946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec_ref(v___x_4951_);
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
    mut v_as_4956_: *mut LeanObject,
    mut v_i_4957_: *mut LeanObject,
    mut v_stop_4958_: *mut LeanObject,
    mut v_b_4959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4960_: usize = 0;
    let mut v_stop_boxed_4961_: usize = 0;
    let mut v_res_4962_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4960_ = lean_unbox_usize(v_i_4957_);
    lean_dec(v_i_4957_);
    v_stop_boxed_4961_ = lean_unbox_usize(v_stop_4958_);
    lean_dec(v_stop_4958_);
    v_res_4962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_4956_, v_i_boxed_4960_, v_stop_boxed_4961_, v_b_4959_);
    lean_dec_ref(v_as_4956_);
    return v_res_4962_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(
    mut v_clause_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: u8 = 0;
    v___x_4964_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_4965_ = lean_unsigned_to_nat(0);
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
                let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
                v___x_4969_ = 0usize;
                v___x_4970_ = lean_usize_of_nat(v___x_4966_);
                v___x_4971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_4963_, v___x_4969_, v___x_4970_, v___x_4964_);
                return v___x_4971_;
            }
        } else {
            let mut v___x_4972_: usize = 0;
            let mut v___x_4973_: usize = 0;
            let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
            v___x_4972_ = 0usize;
            v___x_4973_ = lean_usize_of_nat(v___x_4966_);
            v___x_4974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_4963_, v___x_4972_, v___x_4973_, v___x_4964_);
            return v___x_4974_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(
    mut v_clause_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4976_: *mut LeanObject = core::ptr::null_mut();
    v_res_4976_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_4975_);
    lean_dec_ref(v_clause_4975_);
    return v_res_4976_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(
    mut v_a_4981_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_4981_) {
        0 => {
            let mut v_id_4982_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rupHints_4983_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
            v_id_4982_ = lean_ctor_get(v_a_4981_, 0);
            lean_inc(v_id_4982_);
            v_rupHints_4983_ = lean_ctor_get(v_a_4981_, 1);
            lean_inc_ref(v_rupHints_4983_);
            lean_dec_ref_known(v_a_4981_, 2);
            v___x_4984_ = l_Nat_reprFast(v_id_4982_);
            v___x_4985_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0;
            v___x_4986_ = lean_string_append(v___x_4984_, v___x_4985_);
            v___x_4987_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_4983_);
            lean_dec_ref(v_rupHints_4983_);
            v___x_4988_ = lean_string_append(v___x_4986_, v___x_4987_);
            lean_dec_ref(v___x_4987_);
            v___x_4989_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_4990_ = lean_string_append(v___x_4988_, v___x_4989_);
            return v___x_4990_;
        }
        1 => {
            let mut v_id_4991_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_4992_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rupHints_4993_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
            v_id_4991_ = lean_ctor_get(v_a_4981_, 0);
            lean_inc(v_id_4991_);
            v_c_4992_ = lean_ctor_get(v_a_4981_, 1);
            lean_inc(v_c_4992_);
            v_rupHints_4993_ = lean_ctor_get(v_a_4981_, 2);
            lean_inc_ref(v_rupHints_4993_);
            lean_dec_ref_known(v_a_4981_, 3);
            v___x_4994_ = l_Nat_reprFast(v_id_4991_);
            v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
            v___x_4996_ = lean_string_append(v___x_4994_, v___x_4995_);
            v___x_4997_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_4992_);
            lean_dec(v_c_4992_);
            v___x_4998_ = lean_string_append(v___x_4996_, v___x_4997_);
            lean_dec_ref(v___x_4997_);
            v___x_4999_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
            v___x_5000_ = lean_string_append(v___x_4998_, v___x_4999_);
            v___x_5001_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_4993_);
            lean_dec_ref(v_rupHints_4993_);
            v___x_5002_ = lean_string_append(v___x_5000_, v___x_5001_);
            lean_dec_ref(v___x_5001_);
            v___x_5003_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_5004_ = lean_string_append(v___x_5002_, v___x_5003_);
            return v___x_5004_;
        }
        2 => {
            let mut v_id_5005_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_5006_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rupHints_5007_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ratHints_5008_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
            v_id_5005_ = lean_ctor_get(v_a_4981_, 0);
            lean_inc(v_id_5005_);
            v_c_5006_ = lean_ctor_get(v_a_4981_, 1);
            lean_inc(v_c_5006_);
            v_rupHints_5007_ = lean_ctor_get(v_a_4981_, 3);
            lean_inc_ref(v_rupHints_5007_);
            v_ratHints_5008_ = lean_ctor_get(v_a_4981_, 4);
            lean_inc_ref(v_ratHints_5008_);
            lean_dec_ref_known(v_a_4981_, 5);
            v___x_5009_ = l_Nat_reprFast(v_id_5005_);
            v___x_5010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0;
            v___x_5011_ = lean_string_append(v___x_5009_, v___x_5010_);
            v___x_5012_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_5006_);
            lean_dec(v_c_5006_);
            v___x_5013_ = lean_string_append(v___x_5011_, v___x_5012_);
            lean_dec_ref(v___x_5012_);
            v___x_5014_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
            v___x_5015_ = lean_string_append(v___x_5013_, v___x_5014_);
            v___x_5016_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_5007_);
            lean_dec_ref(v_rupHints_5007_);
            v___x_5017_ = lean_string_append(v___x_5015_, v___x_5016_);
            lean_dec_ref(v___x_5016_);
            v___x_5018_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_5008_);
            lean_dec_ref(v_ratHints_5008_);
            v___x_5019_ = lean_string_append(v___x_5017_, v___x_5018_);
            lean_dec_ref(v___x_5018_);
            v___x_5020_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_5021_ = lean_string_append(v___x_5019_, v___x_5020_);
            return v___x_5021_;
        }
        _ => {
            let mut v_ids_5022_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
            v_ids_5022_ = lean_ctor_get(v_a_4981_, 0);
            lean_inc_ref(v_ids_5022_);
            lean_dec_ref_known(v_a_4981_, 1);
            v___x_5023_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3;
            v___x_5024_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_5022_);
            lean_dec_ref(v_ids_5022_);
            v___x_5025_ = lean_string_append(v___x_5023_, v___x_5024_);
            lean_dec_ref(v___x_5024_);
            v___x_5026_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
            v___x_5027_ = lean_string_append(v___x_5025_, v___x_5026_);
            return v___x_5027_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(
    mut v_as_5029_: *mut LeanObject,
    mut v_i_5030_: usize,
    mut v_stop_5031_: usize,
    mut v_b_5032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5033_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: usize = 0;
    let mut v___x_5040_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5033_ = lean_usize_dec_eq(v_i_5030_, v_stop_5031_);
                if v___x_5033_ == 0 {
                    v___x_5034_ = lean_array_uget_borrowed(v_as_5029_, v_i_5030_);
                    lean_inc(v___x_5034_);
                    v___x_5035_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_5034_);
                    v___x_5036_ = lean_string_append(v_b_5032_, v___x_5035_);
                    lean_dec_ref(v___x_5035_);
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
    mut v_as_5042_: *mut LeanObject,
    mut v_i_5043_: *mut LeanObject,
    mut v_stop_5044_: *mut LeanObject,
    mut v_b_5045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5046_: usize = 0;
    let mut v_stop_boxed_5047_: usize = 0;
    let mut v_res_5048_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5046_ = lean_unbox_usize(v_i_5043_);
    lean_dec(v_i_5043_);
    v_stop_boxed_5047_ = lean_unbox_usize(v_stop_5044_);
    lean_dec(v_stop_5044_);
    v_res_5048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_5042_, v_i_boxed_5046_, v_stop_boxed_5047_, v_b_5045_);
    lean_dec_ref(v_as_5042_);
    return v_res_5048_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToString(
    mut v_proof_5049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: u8 = 0;
    v___x_5050_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0;
    v___x_5051_ = lean_unsigned_to_nat(0);
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
                let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
                v___x_5055_ = 0usize;
                v___x_5056_ = lean_usize_of_nat(v___x_5052_);
                v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_5049_, v___x_5055_, v___x_5056_, v___x_5050_);
                return v___x_5057_;
            }
        } else {
            let mut v___x_5058_: usize = 0;
            let mut v___x_5059_: usize = 0;
            let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
            v___x_5058_ = 0usize;
            v___x_5059_ = lean_usize_of_nat(v___x_5052_);
            v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_5049_, v___x_5058_, v___x_5059_, v___x_5050_);
            return v___x_5060_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(
    mut v_proof_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5062_: *mut LeanObject = core::ptr::null_mut();
    v_res_5062_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_5061_);
    lean_dec_ref(v_proof_5061_);
    return v_res_5062_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(
    mut v_acc_5063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5064_ = lean_uint8_once(
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
    mut v_acc_5066_: *mut LeanObject,
    mut v_lit_5067_: u64,
) -> *mut LeanObject {
    let mut v___y_5069_: u8 = 0;
    let mut v_acc_5070_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_acc_5086_: *mut LeanObject,
    mut v_lit_5087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lit_boxed_5088_: u64 = 0;
    let mut v_res_5089_: *mut LeanObject = core::ptr::null_mut();
    v_lit_boxed_5088_ = lean_unbox_uint64(v_lit_5087_);
    lean_dec_ref(v_lit_5087_);
    v_res_5089_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_5086_, v_lit_boxed_5088_);
    return v_res_5089_;
}
pub unsafe fn l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(
    mut v_msg_5090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    v___x_5091_ = l_ByteArray_empty;
    v___x_5092_ = lean_panic_fn_borrowed(v___x_5091_, v_msg_5090_);
    return v___x_5092_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0()
-> *mut LeanObject {
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    v___x_5093_ = lean_cstr_to_nat(b"18446744073709551615\0".as_ptr().cast());
    return v___x_5093_;
}
pub unsafe fn _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4()
-> *mut LeanObject {
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v___x_5097_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3;
    v___x_5098_ = lean_unsigned_to_nat(4);
    v___x_5099_ = lean_unsigned_to_nat(388);
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
    mut v_acc_5103_: *mut LeanObject,
    mut v_lit_5104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapped_5111_: u64 = 0;
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5113_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
                v___x_5114_ = lean_int_dec_lt(v___x_5113_, v_lit_5104_);
                if v___x_5114_ == 0 {
                    v___x_5115_ = lean_unsigned_to_nat(2);
                    v___x_5116_ = lean_nat_abs(v_lit_5104_);
                    v___x_5117_ = lean_nat_mul(v___x_5115_, v___x_5116_);
                    lean_dec(v___x_5116_);
                    v___x_5118_ = lean_unsigned_to_nat(1);
                    v___x_5119_ = lean_nat_add(v___x_5117_, v___x_5118_);
                    lean_dec(v___x_5117_);
                    v___y_5106_ = v___x_5119_;
                    state = 1;
                    continue;
                } else {
                    v___x_5120_ = lean_unsigned_to_nat(2);
                    v___x_5121_ = lean_nat_abs(v_lit_5104_);
                    v___x_5122_ = lean_nat_mul(v___x_5120_, v___x_5121_);
                    lean_dec(v___x_5121_);
                    v___y_5106_ = v___x_5122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5107_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
                v___x_5108_ = lean_nat_dec_le(v___y_5106_, v___x_5107_);
                if v___x_5108_ == 0 {
                    lean_dec(v___y_5106_);
                    lean_dec_ref(v_acc_5103_);
                    v___x_5109_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4), core::ptr::addr_of_mut!(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once), _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
                    v___x_5110_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_5109_);
                    return v___x_5110_;
                } else {
                    v_mapped_5111_ = lean_uint64_of_nat(v___y_5106_);
                    lean_dec(v___y_5106_);
                    v___x_5112_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_5103_, v_mapped_5111_);
                    return v___x_5112_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(
    mut v_acc_5123_: *mut LeanObject,
    mut v_lit_5124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5125_: *mut LeanObject = core::ptr::null_mut();
    v_res_5125_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5123_, v_lit_5124_);
    lean_dec(v_lit_5124_);
    return v_res_5125_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(
    mut v_acc_5126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    v___x_5127_ = 0;
    v___x_5128_ = lean_byte_array_push(v_acc_5126_, v___x_5127_);
    return v___x_5128_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(
    mut v_acc_5129_: *mut LeanObject,
    mut v_n_5130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    v___x_5131_ = lean_nat_to_int(v_n_5130_);
    v___x_5132_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5129_, v___x_5131_);
    lean_dec(v___x_5131_);
    return v___x_5132_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(
    mut v_acc_5133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    v___x_5134_ = lean_uint8_once(
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
    mut v_as_5136_: *mut LeanObject,
    mut v_i_5137_: usize,
    mut v_stop_5138_: usize,
    mut v_b_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: usize = 0;
    let mut v___x_5145_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5140_ = lean_usize_dec_eq(v_i_5137_, v_stop_5138_);
                if v___x_5140_ == 0 {
                    v___x_5141_ = lean_array_uget_borrowed(v_as_5136_, v_i_5137_);
                    lean_inc(v___x_5141_);
                    v___x_5142_ = lean_nat_to_int(v___x_5141_);
                    v___x_5143_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5139_, v___x_5142_);
                    lean_dec(v___x_5142_);
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
    mut v_as_5147_: *mut LeanObject,
    mut v_i_5148_: *mut LeanObject,
    mut v_stop_5149_: *mut LeanObject,
    mut v_b_5150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5151_: usize = 0;
    let mut v_stop_boxed_5152_: usize = 0;
    let mut v_res_5153_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5151_ = lean_unbox_usize(v_i_5148_);
    lean_dec(v_i_5148_);
    v_stop_boxed_5152_ = lean_unbox_usize(v_stop_5149_);
    lean_dec(v_stop_5149_);
    v_res_5153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_5147_, v_i_boxed_5151_, v_stop_boxed_5152_, v_b_5150_);
    lean_dec_ref(v_as_5147_);
    return v_res_5153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(
    mut v_as_5154_: *mut LeanObject,
    mut v_i_5155_: usize,
    mut v_stop_5156_: usize,
    mut v_b_5157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5158_: u8 = 0;
    v___x_5158_ = lean_usize_dec_eq(v_i_5155_, v_stop_5156_);
    if v___x_5158_ == 0 {
        let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: usize = 0;
        let mut v___x_5163_: usize = 0;
        let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
        v___x_5159_ = lean_array_uget_borrowed(v_as_5154_, v_i_5155_);
        lean_inc(v___x_5159_);
        v___x_5160_ = lean_nat_to_int(v___x_5159_);
        v___x_5161_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5157_, v___x_5160_);
        lean_dec(v___x_5160_);
        v___x_5162_ = 1usize;
        v___x_5163_ = lean_usize_add(v_i_5155_, v___x_5162_);
        v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_5154_, v___x_5163_, v_stop_5156_, v___x_5161_);
        return v___x_5164_;
    } else {
        return v_b_5157_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(
    mut v_as_5165_: *mut LeanObject,
    mut v_i_5166_: *mut LeanObject,
    mut v_stop_5167_: *mut LeanObject,
    mut v_b_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5169_: usize = 0;
    let mut v_stop_boxed_5170_: usize = 0;
    let mut v_res_5171_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5169_ = lean_unbox_usize(v_i_5166_);
    lean_dec(v_i_5166_);
    v_stop_boxed_5170_ = lean_unbox_usize(v_stop_5167_);
    lean_dec(v_stop_5167_);
    v_res_5171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_5165_, v_i_boxed_5169_, v_stop_boxed_5170_, v_b_5168_);
    lean_dec_ref(v_as_5165_);
    return v_res_5171_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(
    mut v_as_5172_: *mut LeanObject,
    mut v_i_5173_: usize,
    mut v_stop_5174_: usize,
    mut v_b_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: usize = 0;
    let mut v___x_5179_: usize = 0;
    let mut v___x_5181_: u8 = 0;
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: u8 = 0;
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: usize = 0;
    let mut v___x_5193_: usize = 0;
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: usize = 0;
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5181_ = lean_usize_dec_eq(v_i_5173_, v_stop_5174_);
                if v___x_5181_ == 0 {
                    v___x_5182_ = lean_array_uget_borrowed(v_as_5172_, v_i_5173_);
                    v_fst_5183_ = lean_ctor_get(v___x_5182_, 0);
                    v_snd_5184_ = lean_ctor_get(v___x_5182_, 1);
                    v___x_5185_ = lean_unsigned_to_nat(0);
                    lean_inc(v_fst_5183_);
                    v___x_5186_ = lean_nat_to_int(v_fst_5183_);
                    v___x_5187_ = lean_int_neg(v___x_5186_);
                    lean_dec(v___x_5186_);
                    v_acc_5188_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5175_, v___x_5187_);
                    lean_dec(v___x_5187_);
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
    mut v_as_5198_: *mut LeanObject,
    mut v_i_5199_: *mut LeanObject,
    mut v_stop_5200_: *mut LeanObject,
    mut v_b_5201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5202_: usize = 0;
    let mut v_stop_boxed_5203_: usize = 0;
    let mut v_res_5204_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5202_ = lean_unbox_usize(v_i_5199_);
    lean_dec(v_i_5199_);
    v_stop_boxed_5203_ = lean_unbox_usize(v_stop_5200_);
    lean_dec(v_stop_5200_);
    v_res_5204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_5198_, v_i_boxed_5202_, v_stop_boxed_5203_, v_b_5201_);
    lean_dec_ref(v_as_5198_);
    return v_res_5204_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(
    mut v_as_5205_: *mut LeanObject,
    mut v_i_5206_: usize,
    mut v_stop_5207_: usize,
    mut v_b_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: usize = 0;
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: u8 = 0;
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: usize = 0;
    let mut v___x_5226_: usize = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: usize = 0;
    let mut v___x_5229_: usize = 0;
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5214_ = lean_usize_dec_eq(v_i_5206_, v_stop_5207_);
                if v___x_5214_ == 0 {
                    v___x_5215_ = lean_array_uget_borrowed(v_as_5205_, v_i_5206_);
                    v_fst_5216_ = lean_ctor_get(v___x_5215_, 0);
                    v_snd_5217_ = lean_ctor_get(v___x_5215_, 1);
                    v___x_5218_ = lean_unsigned_to_nat(0);
                    lean_inc(v_fst_5216_);
                    v___x_5219_ = lean_nat_to_int(v_fst_5216_);
                    v___x_5220_ = lean_int_neg(v___x_5219_);
                    lean_dec(v___x_5219_);
                    v_acc_5221_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_5208_, v___x_5220_);
                    lean_dec(v___x_5220_);
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
    mut v_as_5231_: *mut LeanObject,
    mut v_i_5232_: *mut LeanObject,
    mut v_stop_5233_: *mut LeanObject,
    mut v_b_5234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5235_: usize = 0;
    let mut v_stop_boxed_5236_: usize = 0;
    let mut v_res_5237_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5235_ = lean_unbox_usize(v_i_5232_);
    lean_dec(v_i_5232_);
    v_stop_boxed_5236_ = lean_unbox_usize(v_stop_5233_);
    lean_dec(v_stop_5233_);
    v_res_5237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_5231_, v_i_boxed_5235_, v_stop_boxed_5236_, v_b_5234_);
    lean_dec_ref(v_as_5231_);
    return v_res_5237_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(
    mut v_as_5238_: *mut LeanObject,
    mut v_i_5239_: usize,
    mut v_stop_5240_: usize,
    mut v_b_5241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5242_: u8 = 0;
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_5248_: *mut LeanObject,
    mut v_i_5249_: *mut LeanObject,
    mut v_stop_5250_: *mut LeanObject,
    mut v_b_5251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5252_: usize = 0;
    let mut v_stop_boxed_5253_: usize = 0;
    let mut v_res_5254_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5252_ = lean_unbox_usize(v_i_5249_);
    lean_dec(v_i_5249_);
    v_stop_boxed_5253_ = lean_unbox_usize(v_stop_5250_);
    lean_dec(v_stop_5250_);
    v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_5248_, v_i_boxed_5252_, v_stop_boxed_5253_, v_b_5251_);
    lean_dec_ref(v_as_5248_);
    return v_res_5254_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(
    mut v_proof_5255_: *mut LeanObject,
    mut v_idx_5256_: *mut LeanObject,
    mut v_acc_5257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    let mut v_acc_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v_acc_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: u8 = 0;
    let mut v_acc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: u8 = 0;
    let mut v_acc_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: u8 = 0;
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    let mut v_acc_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: u8 = 0;
    let mut v_acc_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: u8 = 0;
    let mut v___x_5293_: u8 = 0;
    let mut v___x_5294_: usize = 0;
    let mut v___x_5295_: usize = 0;
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: usize = 0;
    let mut v___x_5298_: usize = 0;
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: u8 = 0;
    let mut v_acc_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: u8 = 0;
    let mut v_acc_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: u8 = 0;
    let mut v___x_5314_: u8 = 0;
    let mut v___x_5315_: usize = 0;
    let mut v___x_5316_: usize = 0;
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: usize = 0;
    let mut v___x_5319_: usize = 0;
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: u8 = 0;
    let mut v___x_5324_: usize = 0;
    let mut v___x_5325_: usize = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: usize = 0;
    let mut v___x_5328_: usize = 0;
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: u8 = 0;
    let mut v_acc_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: u8 = 0;
    let mut v___x_5343_: u8 = 0;
    let mut v___x_5344_: usize = 0;
    let mut v___x_5345_: usize = 0;
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v_acc_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: usize = 0;
    let mut v___x_5358_: usize = 0;
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: u8 = 0;
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5366_: usize = 0;
    let mut v___x_5367_: usize = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: usize = 0;
    let mut v___x_5370_: usize = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: u8 = 0;
    let mut v_acc_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: u8 = 0;
    let mut v___x_5379_: usize = 0;
    let mut v___x_5380_: usize = 0;
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: usize = 0;
    let mut v___x_5383_: usize = 0;
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5279_ = lean_array_get_size(v_proof_5255_);
                v___x_5280_ = lean_nat_dec_lt(v_idx_5256_, v___x_5279_);
                if v___x_5280_ == 0 {
                    lean_dec(v_idx_5256_);
                    return v_acc_5257_;
                } else {
                    v___x_5281_ = lean_array_fget_borrowed(v_proof_5255_, v_idx_5256_);
                    match lean_obj_tag(v___x_5281_) {
                        0 => {
                            v_id_5282_ = lean_ctor_get(v___x_5281_, 0);
                            v_rupHints_5283_ = lean_ctor_get(v___x_5281_, 1);
                            v___x_5284_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
                            v_acc_5285_ = lean_byte_array_push(v_acc_5257_, v___x_5284_);
                            lean_inc(v_id_5282_);
                            v___x_5286_ = lean_nat_to_int(v_id_5282_);
                            v_acc_5287_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5285_, v___x_5286_);
                            lean_dec(v___x_5286_);
                            v___x_5288_ = 0;
                            v_acc_5289_ = lean_byte_array_push(v_acc_5287_, v___x_5288_);
                            v___x_5290_ = lean_unsigned_to_nat(0);
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
                            v_id_5300_ = lean_ctor_get(v___x_5281_, 0);
                            v_c_5301_ = lean_ctor_get(v___x_5281_, 1);
                            v_rupHints_5302_ = lean_ctor_get(v___x_5281_, 2);
                            v___x_5303_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
                            v_acc_5304_ = lean_byte_array_push(v_acc_5257_, v___x_5303_);
                            lean_inc(v_id_5300_);
                            v___x_5305_ = lean_nat_to_int(v_id_5300_);
                            v_acc_5306_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5304_, v___x_5305_);
                            lean_dec(v___x_5305_);
                            v___x_5307_ = lean_unsigned_to_nat(0);
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
                            v_id_5330_ = lean_ctor_get(v___x_5281_, 0);
                            v_c_5331_ = lean_ctor_get(v___x_5281_, 1);
                            v_rupHints_5332_ = lean_ctor_get(v___x_5281_, 3);
                            v_ratHints_5333_ = lean_ctor_get(v___x_5281_, 4);
                            v___x_5334_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
                            v_acc_5335_ = lean_byte_array_push(v_acc_5257_, v___x_5334_);
                            lean_inc(v_id_5330_);
                            v___x_5336_ = lean_nat_to_int(v_id_5330_);
                            v_acc_5337_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_5335_, v___x_5336_);
                            lean_dec(v___x_5336_);
                            v___x_5338_ = lean_unsigned_to_nat(0);
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
                            v_ids_5372_ = lean_ctor_get(v___x_5281_, 0);
                            v___x_5373_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once), _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
                            v_acc_5374_ = lean_byte_array_push(v_acc_5257_, v___x_5373_);
                            v___x_5375_ = lean_unsigned_to_nat(0);
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
                v___x_5260_ = lean_unsigned_to_nat(1);
                v___x_5261_ = lean_nat_add(v_idx_5256_, v___x_5260_);
                lean_dec(v_idx_5256_);
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
    mut v_proof_5385_: *mut LeanObject,
    mut v_idx_5386_: *mut LeanObject,
    mut v_acc_5387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5388_: *mut LeanObject = core::ptr::null_mut();
    v_res_5388_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_5385_, v_idx_5386_, v_acc_5387_);
    lean_dec_ref(v_proof_5385_);
    return v_res_5388_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(
    mut v_proof_5389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    v___x_5390_ = lean_unsigned_to_nat(0);
    v___x_5391_ = lean_unsigned_to_nat(4);
    v___x_5392_ = lean_array_get_size(v_proof_5389_);
    v___x_5393_ = lean_nat_mul(v___x_5391_, v___x_5392_);
    v___x_5394_ = lean_mk_empty_byte_array(v___x_5393_);
    lean_dec(v___x_5393_);
    v___x_5395_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_5389_, v___x_5390_, v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(
    mut v_proof_5396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5397_: *mut LeanObject = core::ptr::null_mut();
    v_res_5397_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_5396_);
    lean_dec_ref(v_proof_5396_);
    return v_res_5397_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(
    mut v_path_5398_: *mut LeanObject,
    mut v_proof_5399_: *mut LeanObject,
    mut v_binaryProofs_5400_: u8,
) -> *mut LeanObject {
    if v_binaryProofs_5400_ == 0 {
        let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
        v___x_5402_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_5399_);
        v___x_5403_ = lean_string_to_utf8(v___x_5402_);
        lean_dec_ref(v___x_5402_);
        v___x_5404_ = l_IO_FS_writeBinFile(v_path_5398_, v___x_5403_);
        lean_dec_ref(v___x_5403_);
        return v___x_5404_;
    } else {
        let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
        v___x_5405_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_5399_);
        v___x_5406_ = l_IO_FS_writeBinFile(v_path_5398_, v___x_5405_);
        lean_dec_ref(v___x_5405_);
        return v___x_5406_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(
    mut v_path_5407_: *mut LeanObject,
    mut v_proof_5408_: *mut LeanObject,
    mut v_binaryProofs_5409_: *mut LeanObject,
    mut v_a_5410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binaryProofs_boxed_5411_: u8 = 0;
    let mut v_res_5412_: *mut LeanObject = core::ptr::null_mut();
    v_binaryProofs_boxed_5411_ = (lean_unbox(v_binaryProofs_5409_) as u8);
    v_res_5412_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(
        v_path_5407_,
        v_proof_5408_,
        v_binaryProofs_boxed_5411_,
    );
    lean_dec_ref(v_proof_5408_);
    lean_dec_ref(v_path_5407_);
    return v_res_5412_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
}
