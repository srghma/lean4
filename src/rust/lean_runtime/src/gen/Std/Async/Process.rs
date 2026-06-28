// Lean compiler output
// Module: Std.Async.Process
// Imports: Std.Time Std.Internal.UV.System Std.Data.HashMap Init.Data.Ord.UInt
use crate::r#gen::Init::Control::Basic::l_Functor_mapRev___redArg;
use crate::r#gen::Init::Data::Ord::UInt::{
    initialize_Init_Data_Ord_UInt, runtime_initialize_Init_Data_Ord_UInt,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
use crate::r#gen::Std::Internal::UV::System::{
    initialize_Std_Internal_UV_System, l_Std_Internal_UV_System_getrusage___boxed,
    runtime_initialize_Std_Internal_UV_System,
};
use crate::r#gen::Std::Time::Time::Unit::Millisecond::{
    l_Std_Time_Millisecond_instInhabitedOffset, l_Std_Time_Millisecond_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::lean_uint64_dec_lt;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_to_nat;
use crate::lean_imports_rs::Init::Prelude::{lean_uint64_dec_eq, lean_uint64_of_nat};
use crate::lean_imports_rs::Std::Internal::UV::System::{
    lean_uv_chdir, lean_uv_cwd, lean_uv_exepath, lean_uv_get_available_memory,
    lean_uv_get_constrained_memory, lean_uv_get_free_memory, lean_uv_get_process_title,
    lean_uv_get_total_memory, lean_uv_os_getpid, lean_uv_os_getppid, lean_uv_os_getpriority,
    lean_uv_os_setpriority, lean_uv_set_process_title,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1_value:
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
    m_data: [99, 112, 117, 85, 115, 101, 114, 84, 105, 109, 101, 0],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        99, 112, 117, 83, 121, 115, 116, 101, 109, 84, 105, 109, 101, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13_value:
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
        112, 101, 97, 107, 82, 101, 115, 105, 100, 101, 110, 116, 83, 101, 116, 83, 105, 122, 101,
        75, 98, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        115, 104, 97, 114, 101, 100, 77, 101, 109, 111, 114, 121, 83, 105, 122, 101, 75, 98, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        117, 110, 115, 104, 97, 114, 101, 100, 68, 97, 116, 97, 83, 105, 122, 101, 75, 98, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        117, 110, 115, 104, 97, 114, 101, 100, 83, 116, 97, 99, 107, 83, 105, 122, 101, 75, 98, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        109, 105, 110, 111, 114, 80, 97, 103, 101, 70, 97, 117, 108, 116, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        109, 97, 106, 111, 114, 80, 97, 103, 101, 70, 97, 117, 108, 116, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29_value:
    LeanStringObject<15> = LeanStringObject {
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
        115, 119, 97, 112, 79, 112, 101, 114, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        98, 108, 111, 99, 107, 73, 110, 112, 117, 116, 79, 112, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34_value:
    LeanStringObject<15> = LeanStringObject {
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
        98, 108, 111, 99, 107, 79, 117, 116, 112, 117, 116, 79, 112, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 101, 115, 115, 97, 103, 101, 115, 83, 101, 110, 116, 0],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        109, 101, 115, 115, 97, 103, 101, 115, 82, 101, 99, 101, 105, 118, 101, 100, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        115, 105, 103, 110, 97, 108, 115, 82, 101, 99, 101, 105, 118, 101, 100, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44_value:
    LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        118, 111, 108, 117, 110, 116, 97, 114, 121, 67, 111, 110, 116, 101, 120, 116, 83, 119, 105,
        116, 99, 104, 101, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 118, 111, 108, 117, 110, 116, 97, 114, 121, 67, 111, 110, 116, 101, 120, 116, 83,
        119, 105, 116, 99, 104, 101, 115, 0,
    ],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50_value:
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
    m_data: [32, 125, 0],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50_value
)
    as *mut LeanObject;
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50_value
    ) as *mut LeanObject],
};
static mut l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54: *mut LeanObject = core::ptr::addr_of!(
    l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54_value
)
    as *mut LeanObject;
pub static l_Std_IO_Process_instReprResourceUsageStats___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_IO_Process_instReprResourceUsageStats_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IO_Process_instReprResourceUsageStats___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_IO_Process_instReprResourceUsageStats: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprResourceUsageStats___closed__0_value)
        as *mut LeanObject;
static mut l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0: u64 = 0;
static mut l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_IO_Process_instInhabitedResourceUsageStats_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_IO_Process_instInhabitedResourceUsageStats: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_IO_Process_instInhabitedPId_default: u64 = 0;
pub static mut l_Std_IO_Process_instInhabitedPId: u64 = 0;
pub static l_Std_IO_Process_instOrdPId___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_IO_Process_instOrdPId_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IO_Process_instOrdPId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instOrdPId___closed__0_value) as *mut LeanObject;
pub static mut l_Std_IO_Process_instOrdPId: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instOrdPId___closed__0_value) as *mut LeanObject;
pub static l_Std_IO_Process_instReprPId___lam__0___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [80, 73, 100, 46, 109, 107, 32, 0],
    };
static mut l_Std_IO_Process_instReprPId___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprPId___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_IO_Process_instReprPId___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_IO_Process_instReprPId___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_IO_Process_instReprPId___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprPId___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Std_IO_Process_instReprPId___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_IO_Process_instReprPId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IO_Process_instReprPId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprPId___closed__0_value) as *mut LeanObject;
pub static mut l_Std_IO_Process_instReprPId: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_instReprPId___closed__0_value) as *mut LeanObject;
static mut l_Std_IO_Process_getResourceUsage___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IO_Process_getResourceUsage___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_IO_Process_getResourceUsage___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_IO_Process_getResourceUsage___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IO_Process_getResourceUsage___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_getResourceUsage___closed__1_value) as *mut LeanObject;
pub static l_Std_IO_Process_getResourceUsage___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Internal_UV_System_getrusage___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IO_Process_getResourceUsage___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IO_Process_getResourceUsage___closed__2_value) as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_IO_Process_instReprResourceUsageStats_repr_spec__0(
    mut v_a_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v___x_539_ = lean_nat_to_int(v_a_538_);
    return v___x_539_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    v___x_553_ = lean_unsigned_to_nat(15);
    v___x_554_ = lean_nat_to_int(v___x_553_);
    return v___x_554_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    v___x_561_ = lean_unsigned_to_nat(17);
    v___x_562_ = lean_nat_to_int(v___x_561_);
    return v___x_562_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    v___x_566_ = lean_unsigned_to_nat(25);
    v___x_567_ = lean_nat_to_int(v___x_566_);
    return v___x_567_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18()
-> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = lean_unsigned_to_nat(22);
    v___x_572_ = lean_nat_to_int(v___x_571_);
    return v___x_572_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23()
-> *mut LeanObject {
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    v___x_579_ = lean_unsigned_to_nat(23);
    v___x_580_ = lean_nat_to_int(v___x_579_);
    return v___x_580_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26()
-> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_584_ = lean_unsigned_to_nat(19);
    v___x_585_ = lean_nat_to_int(v___x_584_);
    return v___x_585_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31()
-> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = lean_unsigned_to_nat(18);
    v___x_593_ = lean_nat_to_int(v___x_592_);
    return v___x_593_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38()
-> *mut LeanObject {
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    v___x_603_ = lean_unsigned_to_nat(16);
    v___x_604_ = lean_nat_to_int(v___x_603_);
    return v___x_604_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41()
-> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_unsigned_to_nat(20);
    v___x_609_ = lean_nat_to_int(v___x_608_);
    return v___x_609_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46()
-> *mut LeanObject {
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_616_ = lean_unsigned_to_nat(28);
    v___x_617_ = lean_nat_to_int(v___x_616_);
    return v___x_617_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49()
-> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_621_ = lean_unsigned_to_nat(30);
    v___x_622_ = lean_nat_to_int(v___x_621_);
    return v___x_622_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51()
-> *mut LeanObject {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v___x_624_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0;
    v___x_625_ = lean_string_length(v___x_624_);
    return v___x_625_;
}
pub unsafe fn _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52()
-> *mut LeanObject {
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    v___x_626_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51,
    );
    v___x_627_ = lean_nat_to_int(v___x_626_);
    return v___x_627_;
}
pub unsafe fn l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(
    mut v_x_632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cpuUserTime_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cpuSystemTime_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_peakResidentSetSizeKb_635_: u64 = 0;
    let mut v_sharedMemorySizeKb_636_: u64 = 0;
    let mut v_unsharedDataSizeKb_637_: u64 = 0;
    let mut v_unsharedStackSizeKb_638_: u64 = 0;
    let mut v_minorPageFaults_639_: u64 = 0;
    let mut v_majorPageFaults_640_: u64 = 0;
    let mut v_swapOperations_641_: u64 = 0;
    let mut v_blockInputOps_642_: u64 = 0;
    let mut v_blockOutputOps_643_: u64 = 0;
    let mut v_messagesSent_644_: u64 = 0;
    let mut v_messagesReceived_645_: u64 = 0;
    let mut v_signalsReceived_646_: u64 = 0;
    let mut v_voluntaryContextSwitches_647_: u64 = 0;
    let mut v_involuntaryContextSwitches_648_: u64 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v_cpuUserTime_633_ = lean_ctor_get(v_x_632_, 0);
    v_cpuSystemTime_634_ = lean_ctor_get(v_x_632_, 1);
    v_peakResidentSetSizeKb_635_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_sharedMemorySizeKb_636_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 8) as u32,
    );
    v_unsharedDataSizeKb_637_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
    );
    v_unsharedStackSizeKb_638_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 24) as u32,
    );
    v_minorPageFaults_639_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 32) as u32,
    );
    v_majorPageFaults_640_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 40) as u32,
    );
    v_swapOperations_641_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 48) as u32,
    );
    v_blockInputOps_642_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 56) as u32,
    );
    v_blockOutputOps_643_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 64) as u32,
    );
    v_messagesSent_644_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 72) as u32,
    );
    v_messagesReceived_645_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 80) as u32,
    );
    v_signalsReceived_646_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 88) as u32,
    );
    v_voluntaryContextSwitches_647_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 96) as u32,
    );
    v_involuntaryContextSwitches_648_ = lean_ctor_get_uint64(
        v_x_632_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 104) as u32,
    );
    v___x_649_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5;
    v___x_650_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6;
    v___x_651_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7,
    );
    v___x_652_ = lean_unsigned_to_nat(0);
    v___x_653_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_cpuUserTime_633_, v___x_652_);
    v___x_654_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_654_, 0, v___x_651_);
    lean_ctor_set(v___x_654_, 1, v___x_653_);
    v___x_655_ = 0;
    v___x_656_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_656_, 0, v___x_654_);
    lean_ctor_set_uint8(
        v___x_656_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_657_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_657_, 0, v___x_650_);
    lean_ctor_set(v___x_657_, 1, v___x_656_);
    v___x_658_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9;
    v___x_659_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_659_, 0, v___x_657_);
    lean_ctor_set(v___x_659_, 1, v___x_658_);
    v___x_660_ = lean_box(1);
    v___x_661_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_661_, 0, v___x_659_);
    lean_ctor_set(v___x_661_, 1, v___x_660_);
    v___x_662_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11;
    v___x_663_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_663_, 0, v___x_661_);
    lean_ctor_set(v___x_663_, 1, v___x_662_);
    v___x_664_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_664_, 0, v___x_663_);
    lean_ctor_set(v___x_664_, 1, v___x_649_);
    v___x_665_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12,
    );
    v___x_666_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_cpuSystemTime_634_, v___x_652_);
    v___x_667_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_667_, 0, v___x_665_);
    lean_ctor_set(v___x_667_, 1, v___x_666_);
    v___x_668_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_668_, 0, v___x_667_);
    lean_ctor_set_uint8(
        v___x_668_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_669_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_669_, 0, v___x_664_);
    lean_ctor_set(v___x_669_, 1, v___x_668_);
    v___x_670_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_670_, 0, v___x_669_);
    lean_ctor_set(v___x_670_, 1, v___x_658_);
    v___x_671_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_671_, 0, v___x_670_);
    lean_ctor_set(v___x_671_, 1, v___x_660_);
    v___x_672_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14;
    v___x_673_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_673_, 0, v___x_671_);
    lean_ctor_set(v___x_673_, 1, v___x_672_);
    v___x_674_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_674_, 0, v___x_673_);
    lean_ctor_set(v___x_674_, 1, v___x_649_);
    v___x_675_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15,
    );
    v___x_676_ = lean_uint64_to_nat(v_peakResidentSetSizeKb_635_);
    v___x_677_ = l_Nat_reprFast(v___x_676_);
    v___x_678_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_678_, 0, v___x_677_);
    v___x_679_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_679_, 0, v___x_675_);
    lean_ctor_set(v___x_679_, 1, v___x_678_);
    v___x_680_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_680_, 0, v___x_679_);
    lean_ctor_set_uint8(
        v___x_680_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_681_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_681_, 0, v___x_674_);
    lean_ctor_set(v___x_681_, 1, v___x_680_);
    v___x_682_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_682_, 0, v___x_681_);
    lean_ctor_set(v___x_682_, 1, v___x_658_);
    v___x_683_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_683_, 0, v___x_682_);
    lean_ctor_set(v___x_683_, 1, v___x_660_);
    v___x_684_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17;
    v___x_685_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_685_, 0, v___x_683_);
    lean_ctor_set(v___x_685_, 1, v___x_684_);
    v___x_686_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_686_, 0, v___x_685_);
    lean_ctor_set(v___x_686_, 1, v___x_649_);
    v___x_687_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18,
    );
    v___x_688_ = lean_uint64_to_nat(v_sharedMemorySizeKb_636_);
    v___x_689_ = l_Nat_reprFast(v___x_688_);
    v___x_690_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_690_, 0, v___x_689_);
    v___x_691_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_691_, 0, v___x_687_);
    lean_ctor_set(v___x_691_, 1, v___x_690_);
    v___x_692_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_692_, 0, v___x_691_);
    lean_ctor_set_uint8(
        v___x_692_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_693_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_693_, 0, v___x_686_);
    lean_ctor_set(v___x_693_, 1, v___x_692_);
    v___x_694_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_694_, 0, v___x_693_);
    lean_ctor_set(v___x_694_, 1, v___x_658_);
    v___x_695_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_695_, 0, v___x_694_);
    lean_ctor_set(v___x_695_, 1, v___x_660_);
    v___x_696_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20;
    v___x_697_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_697_, 0, v___x_695_);
    lean_ctor_set(v___x_697_, 1, v___x_696_);
    v___x_698_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_698_, 0, v___x_697_);
    lean_ctor_set(v___x_698_, 1, v___x_649_);
    v___x_699_ = lean_uint64_to_nat(v_unsharedDataSizeKb_637_);
    v___x_700_ = l_Nat_reprFast(v___x_699_);
    v___x_701_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_701_, 0, v___x_700_);
    v___x_702_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_702_, 0, v___x_687_);
    lean_ctor_set(v___x_702_, 1, v___x_701_);
    v___x_703_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_703_, 0, v___x_702_);
    lean_ctor_set_uint8(
        v___x_703_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_704_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_704_, 0, v___x_698_);
    lean_ctor_set(v___x_704_, 1, v___x_703_);
    v___x_705_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_705_, 0, v___x_704_);
    lean_ctor_set(v___x_705_, 1, v___x_658_);
    v___x_706_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_706_, 0, v___x_705_);
    lean_ctor_set(v___x_706_, 1, v___x_660_);
    v___x_707_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22;
    v___x_708_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_708_, 0, v___x_706_);
    lean_ctor_set(v___x_708_, 1, v___x_707_);
    v___x_709_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_709_, 0, v___x_708_);
    lean_ctor_set(v___x_709_, 1, v___x_649_);
    v___x_710_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23,
    );
    v___x_711_ = lean_uint64_to_nat(v_unsharedStackSizeKb_638_);
    v___x_712_ = l_Nat_reprFast(v___x_711_);
    v___x_713_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_713_, 0, v___x_712_);
    v___x_714_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_714_, 0, v___x_710_);
    lean_ctor_set(v___x_714_, 1, v___x_713_);
    v___x_715_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_715_, 0, v___x_714_);
    lean_ctor_set_uint8(
        v___x_715_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_716_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_716_, 0, v___x_709_);
    lean_ctor_set(v___x_716_, 1, v___x_715_);
    v___x_717_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_717_, 0, v___x_716_);
    lean_ctor_set(v___x_717_, 1, v___x_658_);
    v___x_718_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_718_, 0, v___x_717_);
    lean_ctor_set(v___x_718_, 1, v___x_660_);
    v___x_719_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25;
    v___x_720_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_720_, 0, v___x_718_);
    lean_ctor_set(v___x_720_, 1, v___x_719_);
    v___x_721_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_721_, 0, v___x_720_);
    lean_ctor_set(v___x_721_, 1, v___x_649_);
    v___x_722_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26,
    );
    v___x_723_ = lean_uint64_to_nat(v_minorPageFaults_639_);
    v___x_724_ = l_Nat_reprFast(v___x_723_);
    v___x_725_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_725_, 0, v___x_724_);
    v___x_726_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_726_, 0, v___x_722_);
    lean_ctor_set(v___x_726_, 1, v___x_725_);
    v___x_727_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_727_, 0, v___x_726_);
    lean_ctor_set_uint8(
        v___x_727_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_728_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_728_, 0, v___x_721_);
    lean_ctor_set(v___x_728_, 1, v___x_727_);
    v___x_729_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_729_, 0, v___x_728_);
    lean_ctor_set(v___x_729_, 1, v___x_658_);
    v___x_730_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_730_, 0, v___x_729_);
    lean_ctor_set(v___x_730_, 1, v___x_660_);
    v___x_731_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28;
    v___x_732_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_732_, 0, v___x_730_);
    lean_ctor_set(v___x_732_, 1, v___x_731_);
    v___x_733_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_733_, 0, v___x_732_);
    lean_ctor_set(v___x_733_, 1, v___x_649_);
    v___x_734_ = lean_uint64_to_nat(v_majorPageFaults_640_);
    v___x_735_ = l_Nat_reprFast(v___x_734_);
    v___x_736_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_736_, 0, v___x_735_);
    v___x_737_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_737_, 0, v___x_722_);
    lean_ctor_set(v___x_737_, 1, v___x_736_);
    v___x_738_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_738_, 0, v___x_737_);
    lean_ctor_set_uint8(
        v___x_738_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_739_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_739_, 0, v___x_733_);
    lean_ctor_set(v___x_739_, 1, v___x_738_);
    v___x_740_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_740_, 0, v___x_739_);
    lean_ctor_set(v___x_740_, 1, v___x_658_);
    v___x_741_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_741_, 0, v___x_740_);
    lean_ctor_set(v___x_741_, 1, v___x_660_);
    v___x_742_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30;
    v___x_743_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_743_, 0, v___x_741_);
    lean_ctor_set(v___x_743_, 1, v___x_742_);
    v___x_744_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_744_, 0, v___x_743_);
    lean_ctor_set(v___x_744_, 1, v___x_649_);
    v___x_745_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31,
    );
    v___x_746_ = lean_uint64_to_nat(v_swapOperations_641_);
    v___x_747_ = l_Nat_reprFast(v___x_746_);
    v___x_748_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_748_, 0, v___x_747_);
    v___x_749_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_749_, 0, v___x_745_);
    lean_ctor_set(v___x_749_, 1, v___x_748_);
    v___x_750_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_750_, 0, v___x_749_);
    lean_ctor_set_uint8(
        v___x_750_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_751_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_751_, 0, v___x_744_);
    lean_ctor_set(v___x_751_, 1, v___x_750_);
    v___x_752_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_752_, 0, v___x_751_);
    lean_ctor_set(v___x_752_, 1, v___x_658_);
    v___x_753_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_753_, 0, v___x_752_);
    lean_ctor_set(v___x_753_, 1, v___x_660_);
    v___x_754_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33;
    v___x_755_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_755_, 0, v___x_753_);
    lean_ctor_set(v___x_755_, 1, v___x_754_);
    v___x_756_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_756_, 0, v___x_755_);
    lean_ctor_set(v___x_756_, 1, v___x_649_);
    v___x_757_ = lean_uint64_to_nat(v_blockInputOps_642_);
    v___x_758_ = l_Nat_reprFast(v___x_757_);
    v___x_759_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_759_, 0, v___x_758_);
    v___x_760_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_760_, 0, v___x_665_);
    lean_ctor_set(v___x_760_, 1, v___x_759_);
    v___x_761_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_761_, 0, v___x_760_);
    lean_ctor_set_uint8(
        v___x_761_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_762_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_762_, 0, v___x_756_);
    lean_ctor_set(v___x_762_, 1, v___x_761_);
    v___x_763_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_763_, 0, v___x_762_);
    lean_ctor_set(v___x_763_, 1, v___x_658_);
    v___x_764_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_764_, 0, v___x_763_);
    lean_ctor_set(v___x_764_, 1, v___x_660_);
    v___x_765_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35;
    v___x_766_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_766_, 0, v___x_764_);
    lean_ctor_set(v___x_766_, 1, v___x_765_);
    v___x_767_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_767_, 0, v___x_766_);
    lean_ctor_set(v___x_767_, 1, v___x_649_);
    v___x_768_ = lean_uint64_to_nat(v_blockOutputOps_643_);
    v___x_769_ = l_Nat_reprFast(v___x_768_);
    v___x_770_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_770_, 0, v___x_769_);
    v___x_771_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_771_, 0, v___x_745_);
    lean_ctor_set(v___x_771_, 1, v___x_770_);
    v___x_772_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_772_, 0, v___x_771_);
    lean_ctor_set_uint8(
        v___x_772_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_773_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_773_, 0, v___x_767_);
    lean_ctor_set(v___x_773_, 1, v___x_772_);
    v___x_774_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_774_, 0, v___x_773_);
    lean_ctor_set(v___x_774_, 1, v___x_658_);
    v___x_775_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_775_, 0, v___x_774_);
    lean_ctor_set(v___x_775_, 1, v___x_660_);
    v___x_776_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37;
    v___x_777_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_777_, 0, v___x_775_);
    lean_ctor_set(v___x_777_, 1, v___x_776_);
    v___x_778_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_778_, 0, v___x_777_);
    lean_ctor_set(v___x_778_, 1, v___x_649_);
    v___x_779_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38,
    );
    v___x_780_ = lean_uint64_to_nat(v_messagesSent_644_);
    v___x_781_ = l_Nat_reprFast(v___x_780_);
    v___x_782_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_782_, 0, v___x_781_);
    v___x_783_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_783_, 0, v___x_779_);
    lean_ctor_set(v___x_783_, 1, v___x_782_);
    v___x_784_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_784_, 0, v___x_783_);
    lean_ctor_set_uint8(
        v___x_784_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_785_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_785_, 0, v___x_778_);
    lean_ctor_set(v___x_785_, 1, v___x_784_);
    v___x_786_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_786_, 0, v___x_785_);
    lean_ctor_set(v___x_786_, 1, v___x_658_);
    v___x_787_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_787_, 0, v___x_786_);
    lean_ctor_set(v___x_787_, 1, v___x_660_);
    v___x_788_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40;
    v___x_789_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_789_, 0, v___x_787_);
    lean_ctor_set(v___x_789_, 1, v___x_788_);
    v___x_790_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_790_, 0, v___x_789_);
    lean_ctor_set(v___x_790_, 1, v___x_649_);
    v___x_791_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41,
    );
    v___x_792_ = lean_uint64_to_nat(v_messagesReceived_645_);
    v___x_793_ = l_Nat_reprFast(v___x_792_);
    v___x_794_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_794_, 0, v___x_793_);
    v___x_795_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_795_, 0, v___x_791_);
    lean_ctor_set(v___x_795_, 1, v___x_794_);
    v___x_796_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_796_, 0, v___x_795_);
    lean_ctor_set_uint8(
        v___x_796_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_797_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_797_, 0, v___x_790_);
    lean_ctor_set(v___x_797_, 1, v___x_796_);
    v___x_798_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_798_, 0, v___x_797_);
    lean_ctor_set(v___x_798_, 1, v___x_658_);
    v___x_799_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_799_, 0, v___x_798_);
    lean_ctor_set(v___x_799_, 1, v___x_660_);
    v___x_800_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43;
    v___x_801_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_801_, 0, v___x_799_);
    lean_ctor_set(v___x_801_, 1, v___x_800_);
    v___x_802_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_802_, 0, v___x_801_);
    lean_ctor_set(v___x_802_, 1, v___x_649_);
    v___x_803_ = lean_uint64_to_nat(v_signalsReceived_646_);
    v___x_804_ = l_Nat_reprFast(v___x_803_);
    v___x_805_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_805_, 0, v___x_804_);
    v___x_806_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_806_, 0, v___x_722_);
    lean_ctor_set(v___x_806_, 1, v___x_805_);
    v___x_807_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_807_, 0, v___x_806_);
    lean_ctor_set_uint8(
        v___x_807_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_808_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_808_, 0, v___x_802_);
    lean_ctor_set(v___x_808_, 1, v___x_807_);
    v___x_809_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_809_, 0, v___x_808_);
    lean_ctor_set(v___x_809_, 1, v___x_658_);
    v___x_810_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_810_, 0, v___x_809_);
    lean_ctor_set(v___x_810_, 1, v___x_660_);
    v___x_811_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45;
    v___x_812_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_812_, 0, v___x_810_);
    lean_ctor_set(v___x_812_, 1, v___x_811_);
    v___x_813_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_813_, 0, v___x_812_);
    lean_ctor_set(v___x_813_, 1, v___x_649_);
    v___x_814_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46,
    );
    v___x_815_ = lean_uint64_to_nat(v_voluntaryContextSwitches_647_);
    v___x_816_ = l_Nat_reprFast(v___x_815_);
    v___x_817_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_817_, 0, v___x_816_);
    v___x_818_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_818_, 0, v___x_814_);
    lean_ctor_set(v___x_818_, 1, v___x_817_);
    v___x_819_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_819_, 0, v___x_818_);
    lean_ctor_set_uint8(
        v___x_819_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_820_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_820_, 0, v___x_813_);
    lean_ctor_set(v___x_820_, 1, v___x_819_);
    v___x_821_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_821_, 0, v___x_820_);
    lean_ctor_set(v___x_821_, 1, v___x_658_);
    v___x_822_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_822_, 0, v___x_821_);
    lean_ctor_set(v___x_822_, 1, v___x_660_);
    v___x_823_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48;
    v___x_824_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_824_, 0, v___x_822_);
    lean_ctor_set(v___x_824_, 1, v___x_823_);
    v___x_825_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_825_, 0, v___x_824_);
    lean_ctor_set(v___x_825_, 1, v___x_649_);
    v___x_826_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49,
    );
    v___x_827_ = lean_uint64_to_nat(v_involuntaryContextSwitches_648_);
    v___x_828_ = l_Nat_reprFast(v___x_827_);
    v___x_829_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_829_, 0, v___x_828_);
    v___x_830_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_830_, 0, v___x_826_);
    lean_ctor_set(v___x_830_, 1, v___x_829_);
    v___x_831_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_831_, 0, v___x_830_);
    lean_ctor_set_uint8(
        v___x_831_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    v___x_832_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_832_, 0, v___x_825_);
    lean_ctor_set(v___x_832_, 1, v___x_831_);
    v___x_833_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52_once
        ),
        _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52,
    );
    v___x_834_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53;
    v___x_835_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_835_, 0, v___x_834_);
    lean_ctor_set(v___x_835_, 1, v___x_832_);
    v___x_836_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54;
    v___x_837_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_837_, 0, v___x_835_);
    lean_ctor_set(v___x_837_, 1, v___x_836_);
    v___x_838_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_838_, 0, v___x_833_);
    lean_ctor_set(v___x_838_, 1, v___x_837_);
    v___x_839_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_839_, 0, v___x_838_);
    lean_ctor_set_uint8(
        v___x_839_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_655_,
    );
    return v___x_839_;
}
pub unsafe fn l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___boxed(
    mut v_x_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_841_: *mut LeanObject = core::ptr::null_mut();
    v_res_841_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(v_x_840_);
    lean_dec_ref(v_x_840_);
    return v_res_841_;
}
pub unsafe fn l_Std_IO_Process_instReprResourceUsageStats_repr(
    mut v_x_842_: *mut LeanObject,
    mut v_prec_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(v_x_842_);
    return v___x_844_;
}
pub unsafe fn l_Std_IO_Process_instReprResourceUsageStats_repr___boxed(
    mut v_x_845_: *mut LeanObject,
    mut v_prec_846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_847_: *mut LeanObject = core::ptr::null_mut();
    v_res_847_ = l_Std_IO_Process_instReprResourceUsageStats_repr(v_x_845_, v_prec_846_);
    lean_dec(v_prec_846_);
    lean_dec_ref(v_x_845_);
    return v_res_847_;
}
pub unsafe fn _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0() -> u64 {
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u64 = 0;
    v___x_850_ = lean_unsigned_to_nat(0);
    v___x_851_ = lean_uint64_of_nat(v___x_850_);
    return v___x_851_;
}
pub unsafe fn _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1()
-> *mut LeanObject {
    let mut v___x_852_: u64 = 0;
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = lean_uint64_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0_once
        ),
        _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0,
    );
    v___x_853_ = l_Std_Time_Millisecond_instInhabitedOffset;
    v___x_854_ = lean_alloc_ctor(0, 2, (112) as u32);
    lean_ctor_set(v___x_854_, 0, v___x_853_);
    lean_ctor_set(v___x_854_, 1, v___x_853_);
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 8) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 24) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 32) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 40) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 48) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 56) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 64) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 72) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 80) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 88) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 96) as u32,
        v___x_852_,
    );
    lean_ctor_set_uint64(
        v___x_854_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 104) as u32,
        v___x_852_,
    );
    return v___x_854_;
}
pub unsafe fn _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default() -> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1_once
        ),
        _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1,
    );
    return v___x_855_;
}
pub unsafe fn _init_l_Std_IO_Process_instInhabitedResourceUsageStats() -> *mut LeanObject {
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_856_ = l_Std_IO_Process_instInhabitedResourceUsageStats_default;
    return v___x_856_;
}
pub unsafe fn _init_l_Std_IO_Process_instInhabitedPId_default() -> u64 {
    let mut v___x_857_: u64 = 0;
    v___x_857_ = lean_uint64_once(
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0_once
        ),
        _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0,
    );
    return v___x_857_;
}
pub unsafe fn _init_l_Std_IO_Process_instInhabitedPId() -> u64 {
    let mut v___x_858_: u64 = 0;
    v___x_858_ = l_Std_IO_Process_instInhabitedPId_default;
    return v___x_858_;
}
pub unsafe fn l_Std_IO_Process_instDecidableEqPId_decEq(
    mut v_x_859_: u64,
    mut v_x_860_: u64,
) -> u8 {
    let mut v___x_861_: u8 = 0;
    v___x_861_ = lean_uint64_dec_eq(v_x_859_, v_x_860_);
    return v___x_861_;
}
pub unsafe fn l_Std_IO_Process_instDecidableEqPId_decEq___boxed(
    mut v_x_862_: *mut LeanObject,
    mut v_x_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_25__boxed_864_: u64 = 0;
    let mut v_x_26__boxed_865_: u64 = 0;
    let mut v_res_866_: u8 = 0;
    let mut v_r_867_: *mut LeanObject = core::ptr::null_mut();
    v_x_25__boxed_864_ = lean_unbox_uint64(v_x_862_);
    lean_dec_ref(v_x_862_);
    v_x_26__boxed_865_ = lean_unbox_uint64(v_x_863_);
    lean_dec_ref(v_x_863_);
    v_res_866_ = l_Std_IO_Process_instDecidableEqPId_decEq(v_x_25__boxed_864_, v_x_26__boxed_865_);
    v_r_867_ = lean_box((v_res_866_) as usize);
    return v_r_867_;
}
pub unsafe fn l_Std_IO_Process_instDecidableEqPId(mut v_x_868_: u64, mut v_x_869_: u64) -> u8 {
    let mut v___x_870_: u8 = 0;
    v___x_870_ = lean_uint64_dec_eq(v_x_868_, v_x_869_);
    return v___x_870_;
}
pub unsafe fn l_Std_IO_Process_instDecidableEqPId___boxed(
    mut v_x_871_: *mut LeanObject,
    mut v_x_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6__boxed_873_: u64 = 0;
    let mut v_x_7__boxed_874_: u64 = 0;
    let mut v_res_875_: u8 = 0;
    let mut v_r_876_: *mut LeanObject = core::ptr::null_mut();
    v_x_6__boxed_873_ = lean_unbox_uint64(v_x_871_);
    lean_dec_ref(v_x_871_);
    v_x_7__boxed_874_ = lean_unbox_uint64(v_x_872_);
    lean_dec_ref(v_x_872_);
    v_res_875_ = l_Std_IO_Process_instDecidableEqPId(v_x_6__boxed_873_, v_x_7__boxed_874_);
    v_r_876_ = lean_box((v_res_875_) as usize);
    return v_r_876_;
}
pub unsafe fn l_Std_IO_Process_instOrdPId_ord(mut v_x_877_: u64, mut v_x_878_: u64) -> u8 {
    let mut v___x_879_: u8 = 0;
    v___x_879_ = lean_uint64_dec_lt(v_x_877_, v_x_878_);
    if v___x_879_ == 0 {
        let mut v___x_880_: u8 = 0;
        v___x_880_ = lean_uint64_dec_eq(v_x_877_, v_x_878_);
        if v___x_880_ == 0 {
            let mut v___x_881_: u8 = 0;
            v___x_881_ = 2;
            return v___x_881_;
        } else {
            let mut v___x_882_: u8 = 0;
            v___x_882_ = 1;
            return v___x_882_;
        }
    } else {
        let mut v___x_883_: u8 = 0;
        v___x_883_ = 0;
        return v___x_883_;
    }
}
pub unsafe fn l_Std_IO_Process_instOrdPId_ord___boxed(
    mut v_x_884_: *mut LeanObject,
    mut v_x_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_75__boxed_886_: u64 = 0;
    let mut v_x_76__boxed_887_: u64 = 0;
    let mut v_res_888_: u8 = 0;
    let mut v_r_889_: *mut LeanObject = core::ptr::null_mut();
    v_x_75__boxed_886_ = lean_unbox_uint64(v_x_884_);
    lean_dec_ref(v_x_884_);
    v_x_76__boxed_887_ = lean_unbox_uint64(v_x_885_);
    lean_dec_ref(v_x_885_);
    v_res_888_ = l_Std_IO_Process_instOrdPId_ord(v_x_75__boxed_886_, v_x_76__boxed_887_);
    v_r_889_ = lean_box((v_res_888_) as usize);
    return v_r_889_;
}
pub unsafe fn l_Std_IO_Process_instReprPId___lam__0(
    mut v_u_895_: u64,
    mut v___y_896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    v___x_897_ = l_Std_IO_Process_instReprPId___lam__0___closed__1;
    v___x_898_ = lean_uint64_to_nat(v_u_895_);
    v___x_899_ = l_Nat_reprFast(v___x_898_);
    v___x_900_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_900_, 0, v___x_899_);
    v___x_901_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_901_, 0, v___x_897_);
    lean_ctor_set(v___x_901_, 1, v___x_900_);
    v___x_902_ = l_Repr_addAppParen(v___x_901_, v___y_896_);
    return v___x_902_;
}
pub unsafe fn l_Std_IO_Process_instReprPId___lam__0___boxed(
    mut v_u_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_boxed_905_: u64 = 0;
    let mut v_res_906_: *mut LeanObject = core::ptr::null_mut();
    v_u_boxed_905_ = lean_unbox_uint64(v_u_903_);
    lean_dec_ref(v_u_903_);
    v_res_906_ = l_Std_IO_Process_instReprPId___lam__0(v_u_boxed_905_, v___y_904_);
    lean_dec(v___y_904_);
    return v_res_906_;
}
pub unsafe fn l_Std_IO_Process_getProcessTitle() -> *mut LeanObject {
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_uv_get_process_title();
    return v___x_910_;
}
pub unsafe fn l_Std_IO_Process_getProcessTitle___boxed(
    mut v_a_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_912_: *mut LeanObject = core::ptr::null_mut();
    v_res_912_ = l_Std_IO_Process_getProcessTitle();
    return v_res_912_;
}
pub unsafe fn l_Std_IO_Process_setProcessTitle(
    mut v_title_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    v___x_915_ = lean_uv_set_process_title(v_title_913_);
    return v___x_915_;
}
pub unsafe fn l_Std_IO_Process_setProcessTitle___boxed(
    mut v_title_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_918_: *mut LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Std_IO_Process_setProcessTitle(v_title_916_);
    lean_dec_ref(v_title_916_);
    return v_res_918_;
}
pub unsafe fn l_Std_IO_Process_getId() -> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_928_: u8 = 0;
    let mut v_a_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_932_: u8 = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_920_ = lean_uv_os_getpid();
                if lean_obj_tag(v___x_920_) == 0 {
                    v_a_921_ = lean_ctor_get(v___x_920_, 0);
                    v_isSharedCheck_928_ = (!lean_is_exclusive(v___x_920_)) as u8;
                    if v_isSharedCheck_928_ == 0 {
                        v___x_923_ = v___x_920_;
                        v_isShared_924_ = v_isSharedCheck_928_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_921_);
                        lean_dec(v___x_920_);
                        v___x_923_ = lean_box(0);
                        v_isShared_924_ = v_isSharedCheck_928_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_929_ = lean_ctor_get(v___x_920_, 0);
                    v_isSharedCheck_936_ = (!lean_is_exclusive(v___x_920_)) as u8;
                    if v_isSharedCheck_936_ == 0 {
                        v___x_931_ = v___x_920_;
                        v_isShared_932_ = v_isSharedCheck_936_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_929_);
                        lean_dec(v___x_920_);
                        v___x_931_ = lean_box(0);
                        v_isShared_932_ = v_isSharedCheck_936_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_924_ == 0 {
                    v___x_926_ = v___x_923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
                    v___x_926_ = v_reuseFailAlloc_927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_926_;
            }
            3 => {
                if v_isShared_932_ == 0 {
                    v___x_934_ = v___x_931_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
                    v___x_934_ = v_reuseFailAlloc_935_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IO_Process_getId___boxed(mut v_a_937_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_938_: *mut LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Std_IO_Process_getId();
    return v_res_938_;
}
pub unsafe fn l_Std_IO_Process_getParentId() -> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_948_: u8 = 0;
    let mut v_a_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_940_ = lean_uv_os_getppid();
                if lean_obj_tag(v___x_940_) == 0 {
                    v_a_941_ = lean_ctor_get(v___x_940_, 0);
                    v_isSharedCheck_948_ = (!lean_is_exclusive(v___x_940_)) as u8;
                    if v_isSharedCheck_948_ == 0 {
                        v___x_943_ = v___x_940_;
                        v_isShared_944_ = v_isSharedCheck_948_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_941_);
                        lean_dec(v___x_940_);
                        v___x_943_ = lean_box(0);
                        v_isShared_944_ = v_isSharedCheck_948_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_949_ = lean_ctor_get(v___x_940_, 0);
                    v_isSharedCheck_956_ = (!lean_is_exclusive(v___x_940_)) as u8;
                    if v_isSharedCheck_956_ == 0 {
                        v___x_951_ = v___x_940_;
                        v_isShared_952_ = v_isSharedCheck_956_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_949_);
                        lean_dec(v___x_940_);
                        v___x_951_ = lean_box(0);
                        v_isShared_952_ = v_isSharedCheck_956_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_944_ == 0 {
                    v___x_946_ = v___x_943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
                    v___x_946_ = v_reuseFailAlloc_947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_946_;
            }
            3 => {
                if v_isShared_952_ == 0 {
                    v___x_954_ = v___x_951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
                    v___x_954_ = v_reuseFailAlloc_955_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IO_Process_getParentId___boxed(
    mut v_a_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_958_: *mut LeanObject = core::ptr::null_mut();
    v_res_958_ = l_Std_IO_Process_getParentId();
    return v_res_958_;
}
pub unsafe fn l_Std_IO_Process_getCwd() -> *mut LeanObject {
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_968_: u8 = 0;
    let mut v_a_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_972_: u8 = 0;
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_960_ = lean_uv_cwd();
                if lean_obj_tag(v___x_960_) == 0 {
                    v_a_961_ = lean_ctor_get(v___x_960_, 0);
                    v_isSharedCheck_968_ = (!lean_is_exclusive(v___x_960_)) as u8;
                    if v_isSharedCheck_968_ == 0 {
                        v___x_963_ = v___x_960_;
                        v_isShared_964_ = v_isSharedCheck_968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_961_);
                        lean_dec(v___x_960_);
                        v___x_963_ = lean_box(0);
                        v_isShared_964_ = v_isSharedCheck_968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_969_ = lean_ctor_get(v___x_960_, 0);
                    v_isSharedCheck_976_ = (!lean_is_exclusive(v___x_960_)) as u8;
                    if v_isSharedCheck_976_ == 0 {
                        v___x_971_ = v___x_960_;
                        v_isShared_972_ = v_isSharedCheck_976_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_969_);
                        lean_dec(v___x_960_);
                        v___x_971_ = lean_box(0);
                        v_isShared_972_ = v_isSharedCheck_976_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_964_ == 0 {
                    v___x_966_ = v___x_963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
                    v___x_966_ = v_reuseFailAlloc_967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_966_;
            }
            3 => {
                if v_isShared_972_ == 0 {
                    v___x_974_ = v___x_971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
                    v___x_974_ = v_reuseFailAlloc_975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IO_Process_getCwd___boxed(mut v_a_977_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_978_: *mut LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Std_IO_Process_getCwd();
    return v_res_978_;
}
pub unsafe fn l_Std_IO_Process_setCwd(mut v_path_979_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = lean_uv_chdir(v_path_979_);
    return v___x_981_;
}
pub unsafe fn l_Std_IO_Process_setCwd___boxed(
    mut v_path_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_984_: *mut LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Std_IO_Process_setCwd(v_path_982_);
    lean_dec_ref(v_path_982_);
    return v_res_984_;
}
pub unsafe fn l_Std_IO_Process_getPriority(mut v_pid_985_: u64) -> *mut LeanObject {
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_uv_os_getpriority(v_pid_985_);
    return v___x_987_;
}
pub unsafe fn l_Std_IO_Process_getPriority___boxed(
    mut v_pid_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pid_boxed_990_: u64 = 0;
    let mut v_res_991_: *mut LeanObject = core::ptr::null_mut();
    v_pid_boxed_990_ = lean_unbox_uint64(v_pid_988_);
    lean_dec_ref(v_pid_988_);
    v_res_991_ = l_Std_IO_Process_getPriority(v_pid_boxed_990_);
    return v_res_991_;
}
pub unsafe fn l_Std_IO_Process_setPriority(
    mut v_pid_992_: u64,
    mut v_priority_993_: u64,
) -> *mut LeanObject {
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    v___x_995_ = lean_uv_os_setpriority(v_pid_992_, v_priority_993_);
    return v___x_995_;
}
pub unsafe fn l_Std_IO_Process_setPriority___boxed(
    mut v_pid_996_: *mut LeanObject,
    mut v_priority_997_: *mut LeanObject,
    mut v_a_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pid_boxed_999_: u64 = 0;
    let mut v_priority_boxed_1000_: u64 = 0;
    let mut v_res_1001_: *mut LeanObject = core::ptr::null_mut();
    v_pid_boxed_999_ = lean_unbox_uint64(v_pid_996_);
    lean_dec_ref(v_pid_996_);
    v_priority_boxed_1000_ = lean_unbox_uint64(v_priority_997_);
    lean_dec_ref(v_priority_997_);
    v_res_1001_ = l_Std_IO_Process_setPriority(v_pid_boxed_999_, v_priority_boxed_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Std_IO_Process_getResourceUsage___lam__0(
    mut v_rusage_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userTime_1003_: u64 = 0;
    let mut v_systemTime_1004_: u64 = 0;
    let mut v_maxRSS_1005_: u64 = 0;
    let mut v_ixRSS_1006_: u64 = 0;
    let mut v_idRSS_1007_: u64 = 0;
    let mut v_isRSS_1008_: u64 = 0;
    let mut v_minFlt_1009_: u64 = 0;
    let mut v_majFlt_1010_: u64 = 0;
    let mut v_nSwap_1011_: u64 = 0;
    let mut v_inBlock_1012_: u64 = 0;
    let mut v_outBlock_1013_: u64 = 0;
    let mut v_msgSent_1014_: u64 = 0;
    let mut v_msgRecv_1015_: u64 = 0;
    let mut v_signals_1016_: u64 = 0;
    let mut v_voluntaryCS_1017_: u64 = 0;
    let mut v_involuntaryCS_1018_: u64 = 0;
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v_userTime_1003_ = lean_ctor_get_uint64(v_rusage_1002_, 0 as u32);
    v_systemTime_1004_ = lean_ctor_get_uint64(v_rusage_1002_, 8 as u32);
    v_maxRSS_1005_ = lean_ctor_get_uint64(v_rusage_1002_, 16 as u32);
    v_ixRSS_1006_ = lean_ctor_get_uint64(v_rusage_1002_, 24 as u32);
    v_idRSS_1007_ = lean_ctor_get_uint64(v_rusage_1002_, 32 as u32);
    v_isRSS_1008_ = lean_ctor_get_uint64(v_rusage_1002_, 40 as u32);
    v_minFlt_1009_ = lean_ctor_get_uint64(v_rusage_1002_, 48 as u32);
    v_majFlt_1010_ = lean_ctor_get_uint64(v_rusage_1002_, 56 as u32);
    v_nSwap_1011_ = lean_ctor_get_uint64(v_rusage_1002_, 64 as u32);
    v_inBlock_1012_ = lean_ctor_get_uint64(v_rusage_1002_, 72 as u32);
    v_outBlock_1013_ = lean_ctor_get_uint64(v_rusage_1002_, 80 as u32);
    v_msgSent_1014_ = lean_ctor_get_uint64(v_rusage_1002_, 88 as u32);
    v_msgRecv_1015_ = lean_ctor_get_uint64(v_rusage_1002_, 96 as u32);
    v_signals_1016_ = lean_ctor_get_uint64(v_rusage_1002_, 104 as u32);
    v_voluntaryCS_1017_ = lean_ctor_get_uint64(v_rusage_1002_, 112 as u32);
    v_involuntaryCS_1018_ = lean_ctor_get_uint64(v_rusage_1002_, 120 as u32);
    v___x_1019_ = lean_uint64_to_nat(v_userTime_1003_);
    v___x_1020_ = lean_nat_to_int(v___x_1019_);
    v___x_1021_ = lean_uint64_to_nat(v_systemTime_1004_);
    v___x_1022_ = lean_nat_to_int(v___x_1021_);
    v___x_1023_ = lean_alloc_ctor(0, 2, (112) as u32);
    lean_ctor_set(v___x_1023_, 0, v___x_1020_);
    lean_ctor_set(v___x_1023_, 1, v___x_1022_);
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_maxRSS_1005_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 8) as u32,
        v_ixRSS_1006_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 16) as u32,
        v_idRSS_1007_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 24) as u32,
        v_isRSS_1008_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 32) as u32,
        v_minFlt_1009_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 40) as u32,
        v_majFlt_1010_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 48) as u32,
        v_nSwap_1011_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 56) as u32,
        v_inBlock_1012_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 64) as u32,
        v_outBlock_1013_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 72) as u32,
        v_msgSent_1014_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 80) as u32,
        v_msgRecv_1015_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 88) as u32,
        v_signals_1016_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 96) as u32,
        v_voluntaryCS_1017_,
    );
    lean_ctor_set_uint64(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 2 + 104) as u32,
        v_involuntaryCS_1018_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Std_IO_Process_getResourceUsage___lam__0___boxed(
    mut v_rusage_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Std_IO_Process_getResourceUsage___lam__0(v_rusage_1024_);
    lean_dec_ref(v_rusage_1024_);
    return v_res_1025_;
}
pub unsafe fn _init_l_Std_IO_Process_getResourceUsage___closed__0() -> *mut LeanObject {
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    v___x_1026_ = l_instMonadEIO(lean_box(0));
    return v___x_1026_;
}
pub unsafe fn l_Std_IO_Process_getResourceUsage() -> *mut LeanObject {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_28__overap_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    v___x_1030_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IO_Process_getResourceUsage___closed__0),
        core::ptr::addr_of_mut!(l_Std_IO_Process_getResourceUsage___closed__0_once),
        _init_l_Std_IO_Process_getResourceUsage___closed__0,
    );
    v_toApplicative_1031_ = lean_ctor_get(v___x_1030_, 0);
    v_toFunctor_1032_ = lean_ctor_get(v_toApplicative_1031_, 0);
    v___f_1033_ = l_Std_IO_Process_getResourceUsage___closed__1;
    v___x_1034_ = l_Std_IO_Process_getResourceUsage___closed__2;
    lean_inc_ref(v_toFunctor_1032_);
    v___x_28__overap_1035_ = l_Functor_mapRev___redArg(v_toFunctor_1032_, v___x_1034_, v___f_1033_);
    v___x_1036_ = lean_apply_1(v___x_28__overap_1035_, lean_box(0));
    return v___x_1036_;
}
pub unsafe fn l_Std_IO_Process_getResourceUsage___boxed(
    mut v_a_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1038_: *mut LeanObject = core::ptr::null_mut();
    v_res_1038_ = l_Std_IO_Process_getResourceUsage();
    return v_res_1038_;
}
pub unsafe fn l_Std_IO_Process_getExecutablePath() -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1044_: u8 = 0;
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1048_: u8 = 0;
    let mut v_a_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1040_ = lean_uv_exepath();
                if lean_obj_tag(v___x_1040_) == 0 {
                    v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
                    v_isSharedCheck_1048_ = (!lean_is_exclusive(v___x_1040_)) as u8;
                    if v_isSharedCheck_1048_ == 0 {
                        v___x_1043_ = v___x_1040_;
                        v_isShared_1044_ = v_isSharedCheck_1048_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1041_);
                        lean_dec(v___x_1040_);
                        v___x_1043_ = lean_box(0);
                        v_isShared_1044_ = v_isSharedCheck_1048_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1049_ = lean_ctor_get(v___x_1040_, 0);
                    v_isSharedCheck_1056_ = (!lean_is_exclusive(v___x_1040_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1051_ = v___x_1040_;
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1049_);
                        lean_dec(v___x_1040_);
                        v___x_1051_ = lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1044_ == 0 {
                    v___x_1046_ = v___x_1043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
                    v___x_1046_ = v_reuseFailAlloc_1047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1046_;
            }
            3 => {
                if v_isShared_1052_ == 0 {
                    v___x_1054_ = v___x_1051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IO_Process_getExecutablePath___boxed(
    mut v_a_1057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1058_: *mut LeanObject = core::ptr::null_mut();
    v_res_1058_ = l_Std_IO_Process_getExecutablePath();
    return v_res_1058_;
}
pub unsafe fn l_Std_IO_Process_freeMemory() -> *mut LeanObject {
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    v___x_1060_ = lean_uv_get_free_memory();
    return v___x_1060_;
}
pub unsafe fn l_Std_IO_Process_freeMemory___boxed(
    mut v_a_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Std_IO_Process_freeMemory();
    return v_res_1062_;
}
pub unsafe fn l_Std_IO_Process_totalMemory() -> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    v___x_1064_ = lean_uv_get_total_memory();
    return v___x_1064_;
}
pub unsafe fn l_Std_IO_Process_totalMemory___boxed(
    mut v_a_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Std_IO_Process_totalMemory();
    return v_res_1066_;
}
pub unsafe fn l_Std_IO_Process_constrainedMemory() -> *mut LeanObject {
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    v___x_1068_ = lean_uv_get_constrained_memory();
    return v___x_1068_;
}
pub unsafe fn l_Std_IO_Process_constrainedMemory___boxed(
    mut v_a_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1070_: *mut LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_Std_IO_Process_constrainedMemory();
    return v_res_1070_;
}
pub unsafe fn l_Std_IO_Process_availableMemory() -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_uv_get_available_memory();
    return v___x_1072_;
}
pub unsafe fn l_Std_IO_Process_availableMemory___boxed(
    mut v_a_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Std_IO_Process_availableMemory();
    return v_res_1074_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_Process(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_System(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_IO_Process_instInhabitedResourceUsageStats_default =
        _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default();
    lean_mark_persistent(l_Std_IO_Process_instInhabitedResourceUsageStats_default);
    l_Std_IO_Process_instInhabitedResourceUsageStats =
        _init_l_Std_IO_Process_instInhabitedResourceUsageStats();
    lean_mark_persistent(l_Std_IO_Process_instInhabitedResourceUsageStats);
    l_Std_IO_Process_instInhabitedPId_default = _init_l_Std_IO_Process_instInhabitedPId_default();
    l_Std_IO_Process_instInhabitedPId = _init_l_Std_IO_Process_instInhabitedPId();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_Process(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_Process(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Internal_UV_System(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Process(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Async_Process(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Async_Process(builtin);
}
