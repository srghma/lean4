// Lean compiler output
// Module: Std.Internal.UV.System
// Imports: Init.System.Promise Init.Data.SInt Std.Net
use crate::ffi::{
    lean_array_get_size, lean_array_to_list, lean_nat_dec_eq, lean_nat_to_int, lean_string_length,
    lean_uint64_of_nat, lean_uint64_to_nat, lean_uv_chdir, lean_uv_cpu_info, lean_uv_cwd,
    lean_uv_exepath, lean_uv_get_available_memory, lean_uv_get_constrained_memory,
    lean_uv_get_free_memory, lean_uv_get_process_title, lean_uv_get_total_memory,
    lean_uv_getrusage, lean_uv_hrtime, lean_uv_os_environ, lean_uv_os_get_group,
    lean_uv_os_get_passwd, lean_uv_os_getenv, lean_uv_os_gethostname, lean_uv_os_getpid,
    lean_uv_os_getppid, lean_uv_os_getpriority, lean_uv_os_homedir, lean_uv_os_setenv,
    lean_uv_os_setpriority, lean_uv_os_tmpdir, lean_uv_os_uname, lean_uv_os_unsetenv,
    lean_uv_random, lean_uv_set_process_title, lean_uv_uptime,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::SInt::{
    initialize_Init_Data_SInt, runtime_initialize_Init_Data_SInt,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1_value:
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
    m_data: [117, 115, 101, 114, 84, 105, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 121, 115, 116, 101, 109, 84, 105, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 97, 120, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 120, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 115, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 105, 110, 70, 108, 116, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 97, 106, 70, 108, 116, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [110, 83, 119, 97, 112, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 66, 108, 111, 99, 107, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32_value:
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
    m_data: [111, 117, 116, 66, 108, 111, 99, 107, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 115, 103, 83, 101, 110, 116, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 115, 103, 82, 101, 99, 118, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 105, 103, 110, 97, 108, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40_value:
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
    m_data: [118, 111, 108, 117, 110, 116, 97, 114, 121, 67, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43_value:
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
        105, 110, 118, 111, 108, 117, 110, 116, 97, 114, 121, 67, 83, 0,
    ],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46_value:
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
    m_data: [32, 125, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage___closed__0_value:
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
    m_fun: l_Std_Internal_UV_System_instReprRUsage_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_UV_System_instReprRUsage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instReprRUsage: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0: u64 = 0;
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedRUsage_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedRUsage: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [117, 115, 101, 114, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 105, 99, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7_value:
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
    m_data: [115, 121, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 100, 108, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12_value:
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
    m_data: [105, 114, 113, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes___closed__0_value:
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
    m_fun: l_Std_Internal_UV_System_instReprCPUTimes_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instReprCPUTimes: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUTimes_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUTimes: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 111, 100, 101, 108, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 112, 101, 101, 100, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 105, 109, 101, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo___closed__0_value:
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
    m_fun: l_Std_Internal_UV_System_instReprCPUInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instReprCPUInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0_value:
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
    m_data: [117, 115, 101, 114, 110, 97, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4_value:
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
    m_data: [117, 105, 100, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6_value:
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
    m_data: [103, 105, 100, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 104, 101, 108, 108, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [104, 111, 109, 101, 100, 105, 114, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo___closed__0_value:
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
    m_fun: l_Std_Internal_UV_System_instReprPasswdInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instReprPasswdInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value:
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
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedPasswdInfo_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedPasswdInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 114, 111, 117, 112, 110, 97, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 101, 109, 98, 101, 114, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo___closed__0_value:
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
    m_fun: l_Std_Internal_UV_System_instReprGroupInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instReprGroupInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0_value:
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
static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedGroupInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 121, 115, 110, 97, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 108, 101, 97, 115, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 97, 99, 104, 105, 110, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo___closed__0_value:
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
    m_fun: l_Std_Internal_UV_System_instReprUnameInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instReprUnameInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedUnameInfo_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedUnameInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Internal_UV_System_instReprRUsage_repr_spec__0(
    mut v_a_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_977_ = lean_nat_to_int(v_a_976_);
    return v___x_977_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = leanh::lean_unsigned_to_nat(12);
    v___x_992_ = lean_nat_to_int(v___x_991_);
    return v___x_992_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = leanh::lean_unsigned_to_nat(14);
    v___x_1000_ = lean_nat_to_int(v___x_999_);
    return v___x_1000_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = leanh::lean_unsigned_to_nat(10);
    v___x_1005_ = lean_nat_to_int(v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = leanh::lean_unsigned_to_nat(9);
    v___x_1010_ = lean_nat_to_int(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1029_ = leanh::lean_unsigned_to_nat(11);
    v___x_1030_ = lean_nat_to_int(v___x_1029_);
    return v___x_1030_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = leanh::lean_unsigned_to_nat(15);
    v___x_1047_ = lean_nat_to_int(v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = leanh::lean_unsigned_to_nat(17);
    v___x_1052_ = lean_nat_to_int(v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0;
    v___x_1055_ = lean_string_length(v___x_1054_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1056_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47,
    );
    v___x_1057_ = lean_nat_to_int(v___x_1056_);
    return v___x_1057_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr___redArg(
    mut v_x_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_userTime_1063_: u64 = 0;
    let mut v_systemTime_1064_: u64 = 0;
    let mut v_maxRSS_1065_: u64 = 0;
    let mut v_ixRSS_1066_: u64 = 0;
    let mut v_idRSS_1067_: u64 = 0;
    let mut v_isRSS_1068_: u64 = 0;
    let mut v_minFlt_1069_: u64 = 0;
    let mut v_majFlt_1070_: u64 = 0;
    let mut v_nSwap_1071_: u64 = 0;
    let mut v_inBlock_1072_: u64 = 0;
    let mut v_outBlock_1073_: u64 = 0;
    let mut v_msgSent_1074_: u64 = 0;
    let mut v_msgRecv_1075_: u64 = 0;
    let mut v_signals_1076_: u64 = 0;
    let mut v_voluntaryCS_1077_: u64 = 0;
    let mut v_involuntaryCS_1078_: u64 = 0;
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_userTime_1063_ = leanh::lean_ctor_get_uint64(v_x_1062_, 0 as u32);
    v_systemTime_1064_ = leanh::lean_ctor_get_uint64(v_x_1062_, 8 as u32);
    v_maxRSS_1065_ = leanh::lean_ctor_get_uint64(v_x_1062_, 16 as u32);
    v_ixRSS_1066_ = leanh::lean_ctor_get_uint64(v_x_1062_, 24 as u32);
    v_idRSS_1067_ = leanh::lean_ctor_get_uint64(v_x_1062_, 32 as u32);
    v_isRSS_1068_ = leanh::lean_ctor_get_uint64(v_x_1062_, 40 as u32);
    v_minFlt_1069_ = leanh::lean_ctor_get_uint64(v_x_1062_, 48 as u32);
    v_majFlt_1070_ = leanh::lean_ctor_get_uint64(v_x_1062_, 56 as u32);
    v_nSwap_1071_ = leanh::lean_ctor_get_uint64(v_x_1062_, 64 as u32);
    v_inBlock_1072_ = leanh::lean_ctor_get_uint64(v_x_1062_, 72 as u32);
    v_outBlock_1073_ = leanh::lean_ctor_get_uint64(v_x_1062_, 80 as u32);
    v_msgSent_1074_ = leanh::lean_ctor_get_uint64(v_x_1062_, 88 as u32);
    v_msgRecv_1075_ = leanh::lean_ctor_get_uint64(v_x_1062_, 96 as u32);
    v_signals_1076_ = leanh::lean_ctor_get_uint64(v_x_1062_, 104 as u32);
    v_voluntaryCS_1077_ = leanh::lean_ctor_get_uint64(v_x_1062_, 112 as u32);
    v_involuntaryCS_1078_ = leanh::lean_ctor_get_uint64(v_x_1062_, 120 as u32);
    v___x_1079_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1080_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6;
    v___x_1081_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7,
    );
    v___x_1082_ = lean_uint64_to_nat(v_userTime_1063_);
    v___x_1083_ = l_Nat_reprFast(v___x_1082_);
    v___x_1084_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1084_, 0, v___x_1083_);
    v___x_1085_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1085_, 0, v___x_1081_);
    leanh::lean_ctor_set(v___x_1085_, 1, v___x_1084_);
    v___x_1086_ = 0;
    v___x_1087_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1087_, 0, v___x_1085_);
    leanh::lean_ctor_set_uint8(
        v___x_1087_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1088_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1088_, 0, v___x_1080_);
    leanh::lean_ctor_set(v___x_1088_, 1, v___x_1087_);
    v___x_1089_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1090_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1090_, 0, v___x_1088_);
    leanh::lean_ctor_set(v___x_1090_, 1, v___x_1089_);
    v___x_1091_ = leanh::lean_box(1);
    v___x_1092_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1092_, 0, v___x_1090_);
    leanh::lean_ctor_set(v___x_1092_, 1, v___x_1091_);
    v___x_1093_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11;
    v___x_1094_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1094_, 0, v___x_1092_);
    leanh::lean_ctor_set(v___x_1094_, 1, v___x_1093_);
    v___x_1095_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    leanh::lean_ctor_set(v___x_1095_, 1, v___x_1079_);
    v___x_1096_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12,
    );
    v___x_1097_ = lean_uint64_to_nat(v_systemTime_1064_);
    v___x_1098_ = l_Nat_reprFast(v___x_1097_);
    v___x_1099_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1099_, 0, v___x_1098_);
    v___x_1100_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1100_, 0, v___x_1096_);
    leanh::lean_ctor_set(v___x_1100_, 1, v___x_1099_);
    v___x_1101_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1101_, 0, v___x_1100_);
    leanh::lean_ctor_set_uint8(
        v___x_1101_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1102_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1102_, 0, v___x_1095_);
    leanh::lean_ctor_set(v___x_1102_, 1, v___x_1101_);
    v___x_1103_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1103_, 0, v___x_1102_);
    leanh::lean_ctor_set(v___x_1103_, 1, v___x_1089_);
    v___x_1104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    leanh::lean_ctor_set(v___x_1104_, 1, v___x_1091_);
    v___x_1105_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14;
    v___x_1106_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1106_, 0, v___x_1104_);
    leanh::lean_ctor_set(v___x_1106_, 1, v___x_1105_);
    v___x_1107_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    leanh::lean_ctor_set(v___x_1107_, 1, v___x_1079_);
    v___x_1108_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15,
    );
    v___x_1109_ = lean_uint64_to_nat(v_maxRSS_1065_);
    v___x_1110_ = l_Nat_reprFast(v___x_1109_);
    v___x_1111_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    v___x_1112_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1112_, 0, v___x_1108_);
    leanh::lean_ctor_set(v___x_1112_, 1, v___x_1111_);
    v___x_1113_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1113_, 0, v___x_1112_);
    leanh::lean_ctor_set_uint8(
        v___x_1113_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1114_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1114_, 0, v___x_1107_);
    leanh::lean_ctor_set(v___x_1114_, 1, v___x_1113_);
    v___x_1115_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1115_, 0, v___x_1114_);
    leanh::lean_ctor_set(v___x_1115_, 1, v___x_1089_);
    v___x_1116_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1116_, 0, v___x_1115_);
    leanh::lean_ctor_set(v___x_1116_, 1, v___x_1091_);
    v___x_1117_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17;
    v___x_1118_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1118_, 0, v___x_1116_);
    leanh::lean_ctor_set(v___x_1118_, 1, v___x_1117_);
    v___x_1119_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1119_, 0, v___x_1118_);
    leanh::lean_ctor_set(v___x_1119_, 1, v___x_1079_);
    v___x_1120_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18,
    );
    v___x_1121_ = lean_uint64_to_nat(v_ixRSS_1066_);
    v___x_1122_ = l_Nat_reprFast(v___x_1121_);
    v___x_1123_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1123_, 0, v___x_1122_);
    v___x_1124_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1124_, 0, v___x_1120_);
    leanh::lean_ctor_set(v___x_1124_, 1, v___x_1123_);
    v___x_1125_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1125_, 0, v___x_1124_);
    leanh::lean_ctor_set_uint8(
        v___x_1125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1126_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1126_, 0, v___x_1119_);
    leanh::lean_ctor_set(v___x_1126_, 1, v___x_1125_);
    v___x_1127_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    leanh::lean_ctor_set(v___x_1127_, 1, v___x_1089_);
    v___x_1128_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1128_, 0, v___x_1127_);
    leanh::lean_ctor_set(v___x_1128_, 1, v___x_1091_);
    v___x_1129_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20;
    v___x_1130_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1130_, 0, v___x_1128_);
    leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    v___x_1131_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    leanh::lean_ctor_set(v___x_1131_, 1, v___x_1079_);
    v___x_1132_ = lean_uint64_to_nat(v_idRSS_1067_);
    v___x_1133_ = l_Nat_reprFast(v___x_1132_);
    v___x_1134_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1134_, 0, v___x_1133_);
    v___x_1135_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1135_, 0, v___x_1120_);
    leanh::lean_ctor_set(v___x_1135_, 1, v___x_1134_);
    v___x_1136_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1136_, 0, v___x_1135_);
    leanh::lean_ctor_set_uint8(
        v___x_1136_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1137_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1137_, 0, v___x_1131_);
    leanh::lean_ctor_set(v___x_1137_, 1, v___x_1136_);
    v___x_1138_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1138_, 0, v___x_1137_);
    leanh::lean_ctor_set(v___x_1138_, 1, v___x_1089_);
    v___x_1139_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    leanh::lean_ctor_set(v___x_1139_, 1, v___x_1091_);
    v___x_1140_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22;
    v___x_1141_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1141_, 0, v___x_1139_);
    leanh::lean_ctor_set(v___x_1141_, 1, v___x_1140_);
    v___x_1142_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1142_, 0, v___x_1141_);
    leanh::lean_ctor_set(v___x_1142_, 1, v___x_1079_);
    v___x_1143_ = lean_uint64_to_nat(v_isRSS_1068_);
    v___x_1144_ = l_Nat_reprFast(v___x_1143_);
    v___x_1145_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1145_, 0, v___x_1144_);
    v___x_1146_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1146_, 0, v___x_1120_);
    leanh::lean_ctor_set(v___x_1146_, 1, v___x_1145_);
    v___x_1147_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
    leanh::lean_ctor_set_uint8(
        v___x_1147_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1148_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1148_, 0, v___x_1142_);
    leanh::lean_ctor_set(v___x_1148_, 1, v___x_1147_);
    v___x_1149_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1149_, 0, v___x_1148_);
    leanh::lean_ctor_set(v___x_1149_, 1, v___x_1089_);
    v___x_1150_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1150_, 0, v___x_1149_);
    leanh::lean_ctor_set(v___x_1150_, 1, v___x_1091_);
    v___x_1151_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24;
    v___x_1152_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1152_, 0, v___x_1150_);
    leanh::lean_ctor_set(v___x_1152_, 1, v___x_1151_);
    v___x_1153_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1153_, 0, v___x_1152_);
    leanh::lean_ctor_set(v___x_1153_, 1, v___x_1079_);
    v___x_1154_ = lean_uint64_to_nat(v_minFlt_1069_);
    v___x_1155_ = l_Nat_reprFast(v___x_1154_);
    v___x_1156_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
    v___x_1157_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1157_, 0, v___x_1108_);
    leanh::lean_ctor_set(v___x_1157_, 1, v___x_1156_);
    v___x_1158_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
    leanh::lean_ctor_set_uint8(
        v___x_1158_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1159_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1159_, 0, v___x_1153_);
    leanh::lean_ctor_set(v___x_1159_, 1, v___x_1158_);
    v___x_1160_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1160_, 0, v___x_1159_);
    leanh::lean_ctor_set(v___x_1160_, 1, v___x_1089_);
    v___x_1161_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
    leanh::lean_ctor_set(v___x_1161_, 1, v___x_1091_);
    v___x_1162_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26;
    v___x_1163_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1163_, 0, v___x_1161_);
    leanh::lean_ctor_set(v___x_1163_, 1, v___x_1162_);
    v___x_1164_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1164_, 0, v___x_1163_);
    leanh::lean_ctor_set(v___x_1164_, 1, v___x_1079_);
    v___x_1165_ = lean_uint64_to_nat(v_majFlt_1070_);
    v___x_1166_ = l_Nat_reprFast(v___x_1165_);
    v___x_1167_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1167_, 0, v___x_1166_);
    v___x_1168_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1168_, 0, v___x_1108_);
    leanh::lean_ctor_set(v___x_1168_, 1, v___x_1167_);
    v___x_1169_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1169_, 0, v___x_1168_);
    leanh::lean_ctor_set_uint8(
        v___x_1169_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1170_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1170_, 0, v___x_1164_);
    leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
    v___x_1171_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1171_, 0, v___x_1170_);
    leanh::lean_ctor_set(v___x_1171_, 1, v___x_1089_);
    v___x_1172_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1172_, 0, v___x_1171_);
    leanh::lean_ctor_set(v___x_1172_, 1, v___x_1091_);
    v___x_1173_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28;
    v___x_1174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1174_, 0, v___x_1172_);
    leanh::lean_ctor_set(v___x_1174_, 1, v___x_1173_);
    v___x_1175_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1175_, 0, v___x_1174_);
    leanh::lean_ctor_set(v___x_1175_, 1, v___x_1079_);
    v___x_1176_ = lean_uint64_to_nat(v_nSwap_1071_);
    v___x_1177_ = l_Nat_reprFast(v___x_1176_);
    v___x_1178_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1178_, 0, v___x_1177_);
    v___x_1179_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1179_, 0, v___x_1120_);
    leanh::lean_ctor_set(v___x_1179_, 1, v___x_1178_);
    v___x_1180_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1180_, 0, v___x_1179_);
    leanh::lean_ctor_set_uint8(
        v___x_1180_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1181_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1181_, 0, v___x_1175_);
    leanh::lean_ctor_set(v___x_1181_, 1, v___x_1180_);
    v___x_1182_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1182_, 0, v___x_1181_);
    leanh::lean_ctor_set(v___x_1182_, 1, v___x_1089_);
    v___x_1183_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
    leanh::lean_ctor_set(v___x_1183_, 1, v___x_1091_);
    v___x_1184_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30;
    v___x_1185_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1185_, 0, v___x_1183_);
    leanh::lean_ctor_set(v___x_1185_, 1, v___x_1184_);
    v___x_1186_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1186_, 0, v___x_1185_);
    leanh::lean_ctor_set(v___x_1186_, 1, v___x_1079_);
    v___x_1187_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1188_ = lean_uint64_to_nat(v_inBlock_1072_);
    v___x_1189_ = l_Nat_reprFast(v___x_1188_);
    v___x_1190_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1190_, 0, v___x_1189_);
    v___x_1191_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1191_, 0, v___x_1187_);
    leanh::lean_ctor_set(v___x_1191_, 1, v___x_1190_);
    v___x_1192_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1192_, 0, v___x_1191_);
    leanh::lean_ctor_set_uint8(
        v___x_1192_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1193_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1193_, 0, v___x_1186_);
    leanh::lean_ctor_set(v___x_1193_, 1, v___x_1192_);
    v___x_1194_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1194_, 0, v___x_1193_);
    leanh::lean_ctor_set(v___x_1194_, 1, v___x_1089_);
    v___x_1195_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1195_, 0, v___x_1194_);
    leanh::lean_ctor_set(v___x_1195_, 1, v___x_1091_);
    v___x_1196_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33;
    v___x_1197_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1197_, 0, v___x_1195_);
    leanh::lean_ctor_set(v___x_1197_, 1, v___x_1196_);
    v___x_1198_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1198_, 0, v___x_1197_);
    leanh::lean_ctor_set(v___x_1198_, 1, v___x_1079_);
    v___x_1199_ = lean_uint64_to_nat(v_outBlock_1073_);
    v___x_1200_ = l_Nat_reprFast(v___x_1199_);
    v___x_1201_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1201_, 0, v___x_1200_);
    v___x_1202_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1202_, 0, v___x_1081_);
    leanh::lean_ctor_set(v___x_1202_, 1, v___x_1201_);
    v___x_1203_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1203_, 0, v___x_1202_);
    leanh::lean_ctor_set_uint8(
        v___x_1203_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1204_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1204_, 0, v___x_1198_);
    leanh::lean_ctor_set(v___x_1204_, 1, v___x_1203_);
    v___x_1205_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
    leanh::lean_ctor_set(v___x_1205_, 1, v___x_1089_);
    v___x_1206_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1206_, 0, v___x_1205_);
    leanh::lean_ctor_set(v___x_1206_, 1, v___x_1091_);
    v___x_1207_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35;
    v___x_1208_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1208_, 0, v___x_1206_);
    leanh::lean_ctor_set(v___x_1208_, 1, v___x_1207_);
    v___x_1209_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1209_, 0, v___x_1208_);
    leanh::lean_ctor_set(v___x_1209_, 1, v___x_1079_);
    v___x_1210_ = lean_uint64_to_nat(v_msgSent_1074_);
    v___x_1211_ = l_Nat_reprFast(v___x_1210_);
    v___x_1212_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1212_, 0, v___x_1211_);
    v___x_1213_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1213_, 0, v___x_1187_);
    leanh::lean_ctor_set(v___x_1213_, 1, v___x_1212_);
    v___x_1214_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
    leanh::lean_ctor_set_uint8(
        v___x_1214_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1215_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1215_, 0, v___x_1209_);
    leanh::lean_ctor_set(v___x_1215_, 1, v___x_1214_);
    v___x_1216_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
    leanh::lean_ctor_set(v___x_1216_, 1, v___x_1089_);
    v___x_1217_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1217_, 0, v___x_1216_);
    leanh::lean_ctor_set(v___x_1217_, 1, v___x_1091_);
    v___x_1218_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37;
    v___x_1219_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1219_, 0, v___x_1217_);
    leanh::lean_ctor_set(v___x_1219_, 1, v___x_1218_);
    v___x_1220_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
    leanh::lean_ctor_set(v___x_1220_, 1, v___x_1079_);
    v___x_1221_ = lean_uint64_to_nat(v_msgRecv_1075_);
    v___x_1222_ = l_Nat_reprFast(v___x_1221_);
    v___x_1223_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
    v___x_1224_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1224_, 0, v___x_1187_);
    leanh::lean_ctor_set(v___x_1224_, 1, v___x_1223_);
    v___x_1225_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1225_, 0, v___x_1224_);
    leanh::lean_ctor_set_uint8(
        v___x_1225_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1226_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1226_, 0, v___x_1220_);
    leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
    v___x_1227_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1227_, 0, v___x_1226_);
    leanh::lean_ctor_set(v___x_1227_, 1, v___x_1089_);
    v___x_1228_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1228_, 0, v___x_1227_);
    leanh::lean_ctor_set(v___x_1228_, 1, v___x_1091_);
    v___x_1229_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39;
    v___x_1230_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1230_, 0, v___x_1228_);
    leanh::lean_ctor_set(v___x_1230_, 1, v___x_1229_);
    v___x_1231_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1231_, 0, v___x_1230_);
    leanh::lean_ctor_set(v___x_1231_, 1, v___x_1079_);
    v___x_1232_ = lean_uint64_to_nat(v_signals_1076_);
    v___x_1233_ = l_Nat_reprFast(v___x_1232_);
    v___x_1234_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1234_, 0, v___x_1233_);
    v___x_1235_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1235_, 0, v___x_1187_);
    leanh::lean_ctor_set(v___x_1235_, 1, v___x_1234_);
    v___x_1236_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    leanh::lean_ctor_set_uint8(
        v___x_1236_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1237_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1237_, 0, v___x_1231_);
    leanh::lean_ctor_set(v___x_1237_, 1, v___x_1236_);
    v___x_1238_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    leanh::lean_ctor_set(v___x_1238_, 1, v___x_1089_);
    v___x_1239_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    leanh::lean_ctor_set(v___x_1239_, 1, v___x_1091_);
    v___x_1240_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41;
    v___x_1241_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1241_, 0, v___x_1239_);
    leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
    v___x_1242_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1242_, 0, v___x_1241_);
    leanh::lean_ctor_set(v___x_1242_, 1, v___x_1079_);
    v___x_1243_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42,
    );
    v___x_1244_ = lean_uint64_to_nat(v_voluntaryCS_1077_);
    v___x_1245_ = l_Nat_reprFast(v___x_1244_);
    v___x_1246_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1246_, 0, v___x_1245_);
    v___x_1247_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1247_, 0, v___x_1243_);
    leanh::lean_ctor_set(v___x_1247_, 1, v___x_1246_);
    v___x_1248_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    leanh::lean_ctor_set_uint8(
        v___x_1248_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1249_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1249_, 0, v___x_1242_);
    leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
    v___x_1250_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
    leanh::lean_ctor_set(v___x_1250_, 1, v___x_1089_);
    v___x_1251_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1251_, 0, v___x_1250_);
    leanh::lean_ctor_set(v___x_1251_, 1, v___x_1091_);
    v___x_1252_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44;
    v___x_1253_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1253_, 0, v___x_1251_);
    leanh::lean_ctor_set(v___x_1253_, 1, v___x_1252_);
    v___x_1254_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1254_, 0, v___x_1253_);
    leanh::lean_ctor_set(v___x_1254_, 1, v___x_1079_);
    v___x_1255_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45,
    );
    v___x_1256_ = lean_uint64_to_nat(v_involuntaryCS_1078_);
    v___x_1257_ = l_Nat_reprFast(v___x_1256_);
    v___x_1258_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    v___x_1259_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1259_, 0, v___x_1255_);
    leanh::lean_ctor_set(v___x_1259_, 1, v___x_1258_);
    v___x_1260_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1260_, 0, v___x_1259_);
    leanh::lean_ctor_set_uint8(
        v___x_1260_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1261_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1261_, 0, v___x_1254_);
    leanh::lean_ctor_set(v___x_1261_, 1, v___x_1260_);
    v___x_1262_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1263_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1264_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    leanh::lean_ctor_set(v___x_1264_, 1, v___x_1261_);
    v___x_1265_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1266_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1266_, 0, v___x_1264_);
    leanh::lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    v___x_1267_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1267_, 0, v___x_1262_);
    leanh::lean_ctor_set(v___x_1267_, 1, v___x_1266_);
    v___x_1268_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    leanh::lean_ctor_set_uint8(
        v___x_1268_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    return v___x_1268_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr___redArg___boxed(
    mut v_x_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg(v_x_1269_);
    leanh::lean_dec_ref(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr(
    mut v_x_1271_: *mut leanh::LeanObject,
    mut v_prec_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg(v_x_1271_);
    return v___x_1273_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr___boxed(
    mut v_x_1274_: *mut leanh::LeanObject,
    mut v_prec_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Std_Internal_UV_System_instReprRUsage_repr(v_x_1274_, v_prec_1275_);
    leanh::lean_dec(v_prec_1275_);
    leanh::lean_dec_ref(v_x_1274_);
    return v_res_1276_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0() -> u64 {
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u64 = 0;
    v___x_1279_ = leanh::lean_unsigned_to_nat(0);
    v___x_1280_ = lean_uint64_of_nat(v___x_1279_);
    return v___x_1280_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1282_ = leanh::lean_alloc_ctor(0, 0, (128) as u32);
    leanh::lean_ctor_set_uint64(v___x_1282_, 0 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 8 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 16 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 24 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 32 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 40 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 48 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 56 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 64 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 72 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 80 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 88 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 96 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 104 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 112 as u32, v___x_1281_);
    leanh::lean_ctor_set_uint64(v___x_1282_, 120 as u32, v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage_default()
-> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1,
    );
    return v___x_1283_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage() -> *mut leanh::LeanObject
{
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = l_Std_Internal_UV_System_instInhabitedRUsage_default;
    return v___x_1284_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = leanh::lean_unsigned_to_nat(8);
    v___x_1295_ = lean_nat_to_int(v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = leanh::lean_unsigned_to_nat(7);
    v___x_1303_ = lean_nat_to_int(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(
    mut v_x_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_user_1311_: u64 = 0;
    let mut v_nice_1312_: u64 = 0;
    let mut v_sys_1313_: u64 = 0;
    let mut v_idle_1314_: u64 = 0;
    let mut v_irq_1315_: u64 = 0;
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_user_1311_ = leanh::lean_ctor_get_uint64(v_x_1310_, 0 as u32);
    v_nice_1312_ = leanh::lean_ctor_get_uint64(v_x_1310_, 8 as u32);
    v_sys_1313_ = leanh::lean_ctor_get_uint64(v_x_1310_, 16 as u32);
    v_idle_1314_ = leanh::lean_ctor_get_uint64(v_x_1310_, 24 as u32);
    v_irq_1315_ = leanh::lean_ctor_get_uint64(v_x_1310_, 32 as u32);
    v___x_1316_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1317_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3;
    v___x_1318_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4,
    );
    v___x_1319_ = lean_uint64_to_nat(v_user_1311_);
    v___x_1320_ = l_Nat_reprFast(v___x_1319_);
    v___x_1321_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    v___x_1322_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1322_, 0, v___x_1318_);
    leanh::lean_ctor_set(v___x_1322_, 1, v___x_1321_);
    v___x_1323_ = 0;
    v___x_1324_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1324_, 0, v___x_1322_);
    leanh::lean_ctor_set_uint8(
        v___x_1324_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1325_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1325_, 0, v___x_1317_);
    leanh::lean_ctor_set(v___x_1325_, 1, v___x_1324_);
    v___x_1326_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1327_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1327_, 0, v___x_1325_);
    leanh::lean_ctor_set(v___x_1327_, 1, v___x_1326_);
    v___x_1328_ = leanh::lean_box(1);
    v___x_1329_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1329_, 0, v___x_1327_);
    leanh::lean_ctor_set(v___x_1329_, 1, v___x_1328_);
    v___x_1330_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6;
    v___x_1331_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1331_, 0, v___x_1329_);
    leanh::lean_ctor_set(v___x_1331_, 1, v___x_1330_);
    v___x_1332_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1332_, 0, v___x_1331_);
    leanh::lean_ctor_set(v___x_1332_, 1, v___x_1316_);
    v___x_1333_ = lean_uint64_to_nat(v_nice_1312_);
    v___x_1334_ = l_Nat_reprFast(v___x_1333_);
    v___x_1335_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
    v___x_1336_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1336_, 0, v___x_1318_);
    leanh::lean_ctor_set(v___x_1336_, 1, v___x_1335_);
    v___x_1337_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1337_, 0, v___x_1336_);
    leanh::lean_ctor_set_uint8(
        v___x_1337_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1338_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1338_, 0, v___x_1332_);
    leanh::lean_ctor_set(v___x_1338_, 1, v___x_1337_);
    v___x_1339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1339_, 0, v___x_1338_);
    leanh::lean_ctor_set(v___x_1339_, 1, v___x_1326_);
    v___x_1340_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1340_, 0, v___x_1339_);
    leanh::lean_ctor_set(v___x_1340_, 1, v___x_1328_);
    v___x_1341_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8;
    v___x_1342_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1342_, 0, v___x_1340_);
    leanh::lean_ctor_set(v___x_1342_, 1, v___x_1341_);
    v___x_1343_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1343_, 0, v___x_1342_);
    leanh::lean_ctor_set(v___x_1343_, 1, v___x_1316_);
    v___x_1344_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9,
    );
    v___x_1345_ = lean_uint64_to_nat(v_sys_1313_);
    v___x_1346_ = l_Nat_reprFast(v___x_1345_);
    v___x_1347_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1347_, 0, v___x_1346_);
    v___x_1348_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1348_, 0, v___x_1344_);
    leanh::lean_ctor_set(v___x_1348_, 1, v___x_1347_);
    v___x_1349_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1349_, 0, v___x_1348_);
    leanh::lean_ctor_set_uint8(
        v___x_1349_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1350_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1343_);
    leanh::lean_ctor_set(v___x_1350_, 1, v___x_1349_);
    v___x_1351_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1351_, 0, v___x_1350_);
    leanh::lean_ctor_set(v___x_1351_, 1, v___x_1326_);
    v___x_1352_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
    leanh::lean_ctor_set(v___x_1352_, 1, v___x_1328_);
    v___x_1353_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11;
    v___x_1354_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1354_, 0, v___x_1352_);
    leanh::lean_ctor_set(v___x_1354_, 1, v___x_1353_);
    v___x_1355_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1355_, 0, v___x_1354_);
    leanh::lean_ctor_set(v___x_1355_, 1, v___x_1316_);
    v___x_1356_ = lean_uint64_to_nat(v_idle_1314_);
    v___x_1357_ = l_Nat_reprFast(v___x_1356_);
    v___x_1358_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1358_, 0, v___x_1357_);
    v___x_1359_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1359_, 0, v___x_1318_);
    leanh::lean_ctor_set(v___x_1359_, 1, v___x_1358_);
    v___x_1360_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    leanh::lean_ctor_set_uint8(
        v___x_1360_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1361_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1361_, 0, v___x_1355_);
    leanh::lean_ctor_set(v___x_1361_, 1, v___x_1360_);
    v___x_1362_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1362_, 0, v___x_1361_);
    leanh::lean_ctor_set(v___x_1362_, 1, v___x_1326_);
    v___x_1363_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1363_, 0, v___x_1362_);
    leanh::lean_ctor_set(v___x_1363_, 1, v___x_1328_);
    v___x_1364_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13;
    v___x_1365_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1365_, 0, v___x_1363_);
    leanh::lean_ctor_set(v___x_1365_, 1, v___x_1364_);
    v___x_1366_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1366_, 0, v___x_1365_);
    leanh::lean_ctor_set(v___x_1366_, 1, v___x_1316_);
    v___x_1367_ = lean_uint64_to_nat(v_irq_1315_);
    v___x_1368_ = l_Nat_reprFast(v___x_1367_);
    v___x_1369_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    v___x_1370_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1370_, 0, v___x_1344_);
    leanh::lean_ctor_set(v___x_1370_, 1, v___x_1369_);
    v___x_1371_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1371_, 0, v___x_1370_);
    leanh::lean_ctor_set_uint8(
        v___x_1371_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1372_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1372_, 0, v___x_1366_);
    leanh::lean_ctor_set(v___x_1372_, 1, v___x_1371_);
    v___x_1373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1374_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1375_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1375_, 0, v___x_1374_);
    leanh::lean_ctor_set(v___x_1375_, 1, v___x_1372_);
    v___x_1376_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1377_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1377_, 0, v___x_1375_);
    leanh::lean_ctor_set(v___x_1377_, 1, v___x_1376_);
    v___x_1378_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1378_, 0, v___x_1373_);
    leanh::lean_ctor_set(v___x_1378_, 1, v___x_1377_);
    v___x_1379_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1379_, 0, v___x_1378_);
    leanh::lean_ctor_set_uint8(
        v___x_1379_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    return v___x_1379_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___boxed(
    mut v_x_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1381_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(v_x_1380_);
    leanh::lean_dec_ref(v_x_1380_);
    return v_res_1381_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr(
    mut v_x_1382_: *mut leanh::LeanObject,
    mut v_prec_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(v_x_1382_);
    return v___x_1384_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr___boxed(
    mut v_x_1385_: *mut leanh::LeanObject,
    mut v_prec_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Std_Internal_UV_System_instReprCPUTimes_repr(v_x_1385_, v_prec_1386_);
    leanh::lean_dec(v_prec_1386_);
    leanh::lean_dec_ref(v_x_1385_);
    return v_res_1387_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1390_: u64 = 0;
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1391_ = leanh::lean_alloc_ctor(0, 0, (40) as u32);
    leanh::lean_ctor_set_uint64(v___x_1391_, 0 as u32, v___x_1390_);
    leanh::lean_ctor_set_uint64(v___x_1391_, 8 as u32, v___x_1390_);
    leanh::lean_ctor_set_uint64(v___x_1391_, 16 as u32, v___x_1390_);
    leanh::lean_ctor_set_uint64(v___x_1391_, 24 as u32, v___x_1390_);
    leanh::lean_ctor_set_uint64(v___x_1391_, 32 as u32, v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default()
-> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0,
    );
    return v___x_1392_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUTimes() -> *mut leanh::LeanObject
{
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Std_Internal_UV_System_instInhabitedCPUTimes_default;
    return v___x_1393_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg(
    mut v_x_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_model_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_speed_1411_: u64 = 0;
    let mut v_times_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_model_1410_ = leanh::lean_ctor_get(v_x_1409_, 0);
    leanh::lean_inc_ref(v_model_1410_);
    v_speed_1411_ = leanh::lean_ctor_get_uint64(
        v_x_1409_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_times_1412_ = leanh::lean_ctor_get(v_x_1409_, 1);
    leanh::lean_inc_ref(v_times_1412_);
    leanh::lean_dec_ref(v_x_1409_);
    v___x_1413_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1414_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3;
    v___x_1415_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18,
    );
    v___x_1416_ = l_String_quote(v_model_1410_);
    v___x_1417_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1417_, 0, v___x_1416_);
    v___x_1418_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1418_, 0, v___x_1415_);
    leanh::lean_ctor_set(v___x_1418_, 1, v___x_1417_);
    v___x_1419_ = 0;
    v___x_1420_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1420_, 0, v___x_1418_);
    leanh::lean_ctor_set_uint8(
        v___x_1420_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    v___x_1421_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1421_, 0, v___x_1414_);
    leanh::lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    v___x_1422_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1423_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1423_, 0, v___x_1421_);
    leanh::lean_ctor_set(v___x_1423_, 1, v___x_1422_);
    v___x_1424_ = leanh::lean_box(1);
    v___x_1425_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1425_, 0, v___x_1423_);
    leanh::lean_ctor_set(v___x_1425_, 1, v___x_1424_);
    v___x_1426_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5;
    v___x_1427_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1427_, 0, v___x_1425_);
    leanh::lean_ctor_set(v___x_1427_, 1, v___x_1426_);
    v___x_1428_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1428_, 0, v___x_1427_);
    leanh::lean_ctor_set(v___x_1428_, 1, v___x_1413_);
    v___x_1429_ = lean_uint64_to_nat(v_speed_1411_);
    v___x_1430_ = l_Nat_reprFast(v___x_1429_);
    v___x_1431_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1431_, 0, v___x_1430_);
    v___x_1432_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1432_, 0, v___x_1415_);
    leanh::lean_ctor_set(v___x_1432_, 1, v___x_1431_);
    v___x_1433_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1433_, 0, v___x_1432_);
    leanh::lean_ctor_set_uint8(
        v___x_1433_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    v___x_1434_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1434_, 0, v___x_1428_);
    leanh::lean_ctor_set(v___x_1434_, 1, v___x_1433_);
    v___x_1435_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    leanh::lean_ctor_set(v___x_1435_, 1, v___x_1422_);
    v___x_1436_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
    leanh::lean_ctor_set(v___x_1436_, 1, v___x_1424_);
    v___x_1437_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7;
    v___x_1438_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1438_, 0, v___x_1436_);
    leanh::lean_ctor_set(v___x_1438_, 1, v___x_1437_);
    v___x_1439_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 1, v___x_1413_);
    v___x_1440_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(v_times_1412_);
    leanh::lean_dec_ref(v_times_1412_);
    v___x_1441_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1441_, 0, v___x_1415_);
    leanh::lean_ctor_set(v___x_1441_, 1, v___x_1440_);
    v___x_1442_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    leanh::lean_ctor_set_uint8(
        v___x_1442_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    v___x_1443_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1443_, 0, v___x_1439_);
    leanh::lean_ctor_set(v___x_1443_, 1, v___x_1442_);
    v___x_1444_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1445_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1446_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    leanh::lean_ctor_set(v___x_1446_, 1, v___x_1443_);
    v___x_1447_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1448_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1448_, 0, v___x_1446_);
    leanh::lean_ctor_set(v___x_1448_, 1, v___x_1447_);
    v___x_1449_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1449_, 0, v___x_1444_);
    leanh::lean_ctor_set(v___x_1449_, 1, v___x_1448_);
    v___x_1450_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    leanh::lean_ctor_set_uint8(
        v___x_1450_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    return v___x_1450_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUInfo_repr(
    mut v_x_1451_: *mut leanh::LeanObject,
    mut v_prec_1452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg(v_x_1451_);
    return v___x_1453_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUInfo_repr___boxed(
    mut v_x_1454_: *mut leanh::LeanObject,
    mut v_prec_1455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Std_Internal_UV_System_instReprCPUInfo_repr(v_x_1454_, v_prec_1455_);
    leanh::lean_dec(v_prec_1455_);
    return v_res_1456_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u64 = 0;
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Std_Internal_UV_System_instInhabitedCPUTimes_default;
    v___x_1461_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1462_ = l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0;
    v___x_1463_ = leanh::lean_alloc_ctor(0, 2, (8) as u32);
    leanh::lean_ctor_set(v___x_1463_, 0, v___x_1462_);
    leanh::lean_ctor_set(v___x_1463_, 1, v___x_1460_);
    leanh::lean_ctor_set_uint64(
        v___x_1463_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1461_,
    );
    return v___x_1463_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1,
    );
    return v___x_1464_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUInfo() -> *mut leanh::LeanObject
{
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Std_Internal_UV_System_instInhabitedCPUInfo_default;
    return v___x_1465_;
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
    mut v_x_1472_: *mut leanh::LeanObject,
    mut v_x_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u64 = 0;
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1472_) == 0 {
                    v___x_1474_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1;
                    return v___x_1474_;
                } else {
                    v_val_1475_ = leanh::lean_ctor_get(v_x_1472_, 0);
                    v_isSharedCheck_1488_ = (!leanh::lean_is_exclusive(v_x_1472_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1477_ = v_x_1472_;
                        v_isShared_1478_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1475_);
                        leanh::lean_dec(v_x_1472_);
                        v___x_1477_ = leanh::lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1479_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3;
                v___x_1480_ = leanh::lean_unbox_uint64(v_val_1475_);
                leanh::lean_dec(v_val_1475_);
                v___x_1481_ = lean_uint64_to_nat(v___x_1480_);
                v___x_1482_ = l_Nat_reprFast(v___x_1481_);
                if v_isShared_1478_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1477_, 3);
                    leanh::lean_ctor_set(v___x_1477_, 0, v___x_1482_);
                    v___x_1484_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1482_);
                    v___x_1484_ = v_reuseFailAlloc_1487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1485_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1485_, 0, v___x_1479_);
                leanh::lean_ctor_set(v___x_1485_, 1, v___x_1484_);
                v___x_1486_ = l_Repr_addAppParen(v___x_1485_, v_x_1473_);
                return v___x_1486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___boxed(
    mut v_x_1489_: *mut leanh::LeanObject,
    mut v_x_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
        v_x_1489_, v_x_1490_,
    );
    leanh::lean_dec(v_x_1490_);
    return v_res_1491_;
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
    mut v_x_1492_: *mut leanh::LeanObject,
    mut v_x_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1492_) == 0 {
                    v___x_1494_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1;
                    return v___x_1494_;
                } else {
                    v_val_1495_ = leanh::lean_ctor_get(v_x_1492_, 0);
                    v_isSharedCheck_1506_ = (!leanh::lean_is_exclusive(v_x_1492_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1497_ = v_x_1492_;
                        v_isShared_1498_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1495_);
                        leanh::lean_dec(v_x_1492_);
                        v___x_1497_ = leanh::lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1499_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3;
                v___x_1500_ = l_String_quote(v_val_1495_);
                if v_isShared_1498_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1497_, 3);
                    leanh::lean_ctor_set(v___x_1497_, 0, v___x_1500_);
                    v___x_1502_ = v___x_1497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1500_);
                    v___x_1502_ = v_reuseFailAlloc_1505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1503_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1503_, 0, v___x_1499_);
                leanh::lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                v___x_1504_ = l_Repr_addAppParen(v___x_1503_, v_x_1493_);
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1___boxed(
    mut v_x_1507_: *mut leanh::LeanObject,
    mut v_x_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1509_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
        v_x_1507_, v_x_1508_,
    );
    leanh::lean_dec(v_x_1508_);
    return v_res_1509_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg(
    mut v_x_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_username_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uid_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gid_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shell_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homedir_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_username_1532_ = leanh::lean_ctor_get(v_x_1531_, 0);
    leanh::lean_inc_ref(v_username_1532_);
    v_uid_1533_ = leanh::lean_ctor_get(v_x_1531_, 1);
    leanh::lean_inc(v_uid_1533_);
    v_gid_1534_ = leanh::lean_ctor_get(v_x_1531_, 2);
    leanh::lean_inc(v_gid_1534_);
    v_shell_1535_ = leanh::lean_ctor_get(v_x_1531_, 3);
    leanh::lean_inc(v_shell_1535_);
    v_homedir_1536_ = leanh::lean_ctor_get(v_x_1531_, 4);
    leanh::lean_inc(v_homedir_1536_);
    leanh::lean_dec_ref(v_x_1531_);
    v___x_1537_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1538_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3;
    v___x_1539_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7,
    );
    v___x_1540_ = l_String_quote(v_username_1532_);
    v___x_1541_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1541_, 0, v___x_1540_);
    v___x_1542_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1542_, 0, v___x_1539_);
    leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
    v___x_1543_ = 0;
    v___x_1544_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1544_, 0, v___x_1542_);
    leanh::lean_ctor_set_uint8(
        v___x_1544_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1545_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1545_, 0, v___x_1538_);
    leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    v___x_1546_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1547_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1547_, 0, v___x_1545_);
    leanh::lean_ctor_set(v___x_1547_, 1, v___x_1546_);
    v___x_1548_ = leanh::lean_box(1);
    v___x_1549_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1549_, 0, v___x_1547_);
    leanh::lean_ctor_set(v___x_1549_, 1, v___x_1548_);
    v___x_1550_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5;
    v___x_1551_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1551_, 0, v___x_1549_);
    leanh::lean_ctor_set(v___x_1551_, 1, v___x_1550_);
    v___x_1552_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1552_, 0, v___x_1551_);
    leanh::lean_ctor_set(v___x_1552_, 1, v___x_1537_);
    v___x_1553_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9,
    );
    v___x_1554_ = leanh::lean_unsigned_to_nat(0);
    v___x_1555_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
        v_uid_1533_,
        v___x_1554_,
    );
    v___x_1556_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1556_, 0, v___x_1553_);
    leanh::lean_ctor_set(v___x_1556_, 1, v___x_1555_);
    v___x_1557_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    leanh::lean_ctor_set_uint8(
        v___x_1557_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1558_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1558_, 0, v___x_1552_);
    leanh::lean_ctor_set(v___x_1558_, 1, v___x_1557_);
    v___x_1559_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1559_, 0, v___x_1558_);
    leanh::lean_ctor_set(v___x_1559_, 1, v___x_1546_);
    v___x_1560_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1560_, 0, v___x_1559_);
    leanh::lean_ctor_set(v___x_1560_, 1, v___x_1548_);
    v___x_1561_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7;
    v___x_1562_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1562_, 0, v___x_1560_);
    leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
    v___x_1563_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1563_, 0, v___x_1562_);
    leanh::lean_ctor_set(v___x_1563_, 1, v___x_1537_);
    v___x_1564_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
        v_gid_1534_,
        v___x_1554_,
    );
    v___x_1565_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1565_, 0, v___x_1553_);
    leanh::lean_ctor_set(v___x_1565_, 1, v___x_1564_);
    v___x_1566_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1566_, 0, v___x_1565_);
    leanh::lean_ctor_set_uint8(
        v___x_1566_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1567_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1567_, 0, v___x_1563_);
    leanh::lean_ctor_set(v___x_1567_, 1, v___x_1566_);
    v___x_1568_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1568_, 0, v___x_1567_);
    leanh::lean_ctor_set(v___x_1568_, 1, v___x_1546_);
    v___x_1569_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1569_, 0, v___x_1568_);
    leanh::lean_ctor_set(v___x_1569_, 1, v___x_1548_);
    v___x_1570_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9;
    v___x_1571_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1571_, 0, v___x_1569_);
    leanh::lean_ctor_set(v___x_1571_, 1, v___x_1570_);
    v___x_1572_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1572_, 0, v___x_1571_);
    leanh::lean_ctor_set(v___x_1572_, 1, v___x_1537_);
    v___x_1573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18,
    );
    v___x_1574_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
        v_shell_1535_,
        v___x_1554_,
    );
    v___x_1575_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1575_, 0, v___x_1573_);
    leanh::lean_ctor_set(v___x_1575_, 1, v___x_1574_);
    v___x_1576_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1576_, 0, v___x_1575_);
    leanh::lean_ctor_set_uint8(
        v___x_1576_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1577_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1577_, 0, v___x_1572_);
    leanh::lean_ctor_set(v___x_1577_, 1, v___x_1576_);
    v___x_1578_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1578_, 0, v___x_1577_);
    leanh::lean_ctor_set(v___x_1578_, 1, v___x_1546_);
    v___x_1579_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1579_, 0, v___x_1578_);
    leanh::lean_ctor_set(v___x_1579_, 1, v___x_1548_);
    v___x_1580_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11;
    v___x_1581_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1581_, 0, v___x_1579_);
    leanh::lean_ctor_set(v___x_1581_, 1, v___x_1580_);
    v___x_1582_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    leanh::lean_ctor_set(v___x_1582_, 1, v___x_1537_);
    v___x_1583_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1584_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
        v_homedir_1536_,
        v___x_1554_,
    );
    v___x_1585_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1585_, 0, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 1, v___x_1584_);
    v___x_1586_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    leanh::lean_ctor_set_uint8(
        v___x_1586_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1587_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1587_, 0, v___x_1582_);
    leanh::lean_ctor_set(v___x_1587_, 1, v___x_1586_);
    v___x_1588_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1589_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1590_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
    leanh::lean_ctor_set(v___x_1590_, 1, v___x_1587_);
    v___x_1591_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1592_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1592_, 0, v___x_1590_);
    leanh::lean_ctor_set(v___x_1592_, 1, v___x_1591_);
    v___x_1593_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1593_, 0, v___x_1588_);
    leanh::lean_ctor_set(v___x_1593_, 1, v___x_1592_);
    v___x_1594_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1594_, 0, v___x_1593_);
    leanh::lean_ctor_set_uint8(
        v___x_1594_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    return v___x_1594_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprPasswdInfo_repr(
    mut v_x_1595_: *mut leanh::LeanObject,
    mut v_prec_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg(v_x_1595_);
    return v___x_1597_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprPasswdInfo_repr___boxed(
    mut v_x_1598_: *mut leanh::LeanObject,
    mut v_prec_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr(v_x_1598_, v_prec_1599_);
    leanh::lean_dec(v_prec_1599_);
    return v_res_1600_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1608_: *mut leanh::LeanObject,
    mut v_x_1609_: *mut leanh::LeanObject,
    mut v_x_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1610_) == 0 {
                    leanh::lean_dec(v_x_1608_);
                    return v_x_1609_;
                } else {
                    v_head_1611_ = leanh::lean_ctor_get(v_x_1610_, 0);
                    v_tail_1612_ = leanh::lean_ctor_get(v_x_1610_, 1);
                    v_isSharedCheck_1623_ = (!leanh::lean_is_exclusive(v_x_1610_)) as u8;
                    if v_isSharedCheck_1623_ == 0 {
                        v___x_1614_ = v_x_1610_;
                        v_isShared_1615_ = v_isSharedCheck_1623_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1612_);
                        leanh::lean_inc(v_head_1611_);
                        leanh::lean_dec(v_x_1610_);
                        v___x_1614_ = leanh::lean_box(0);
                        v_isShared_1615_ = v_isSharedCheck_1623_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1608_);
                if v_isShared_1615_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1614_, 5);
                    leanh::lean_ctor_set(v___x_1614_, 1, v_x_1608_);
                    leanh::lean_ctor_set(v___x_1614_, 0, v_x_1609_);
                    v___x_1617_ = v___x_1614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_x_1609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_x_1608_);
                    v___x_1617_ = v_reuseFailAlloc_1622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1618_ = l_String_quote(v_head_1611_);
                v___x_1619_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                v___x_1620_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1620_, 0, v___x_1617_);
                leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v_x_1609_ = v___x_1620_;
                v_x_1610_ = v_tail_1612_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(
    mut v_x_1624_: *mut leanh::LeanObject,
    mut v_x_1625_: *mut leanh::LeanObject,
    mut v_x_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1626_) == 0 {
                    leanh::lean_dec(v_x_1624_);
                    return v_x_1625_;
                } else {
                    v_head_1627_ = leanh::lean_ctor_get(v_x_1626_, 0);
                    v_tail_1628_ = leanh::lean_ctor_get(v_x_1626_, 1);
                    v_isSharedCheck_1639_ = (!leanh::lean_is_exclusive(v_x_1626_)) as u8;
                    if v_isSharedCheck_1639_ == 0 {
                        v___x_1630_ = v_x_1626_;
                        v_isShared_1631_ = v_isSharedCheck_1639_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1628_);
                        leanh::lean_inc(v_head_1627_);
                        leanh::lean_dec(v_x_1626_);
                        v___x_1630_ = leanh::lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1624_);
                if v_isShared_1631_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1630_, 5);
                    leanh::lean_ctor_set(v___x_1630_, 1, v_x_1624_);
                    leanh::lean_ctor_set(v___x_1630_, 0, v_x_1625_);
                    v___x_1633_ = v___x_1630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_x_1625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_x_1624_);
                    v___x_1633_ = v_reuseFailAlloc_1638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1634_ = l_String_quote(v_head_1627_);
                v___x_1635_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1635_, 0, v___x_1634_);
                v___x_1636_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1636_, 0, v___x_1633_);
                leanh::lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                v___x_1637_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(v_x_1624_, v___x_1636_, v_tail_1628_);
                return v___x_1637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_String_quote(v___y_1640_);
    v___x_1642_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1642_, 0, v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0(
    mut v_x_1643_: *mut leanh::LeanObject,
    mut v_x_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1643_) == 0 {
        let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1644_);
        v___x_1645_ = leanh::lean_box(0);
        return v___x_1645_;
    } else {
        let mut v_tail_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1646_ = leanh::lean_ctor_get(v_x_1643_, 1);
        if leanh::lean_obj_tag(v_tail_1646_) == 0 {
            let mut v_head_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1644_);
            v_head_1647_ = leanh::lean_ctor_get(v_x_1643_, 0);
            leanh::lean_inc(v_head_1647_);
            leanh::lean_dec_ref_known(v_x_1643_, 2);
            v___x_1648_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1647_);
            return v___x_1648_;
        } else {
            let mut v_head_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1646_);
            v_head_1649_ = leanh::lean_ctor_get(v_x_1643_, 0);
            leanh::lean_inc(v_head_1649_);
            leanh::lean_dec_ref_known(v_x_1643_, 2);
            v___x_1650_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1649_);
            v___x_1651_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(v_x_1644_, v___x_1650_, v_tail_1646_);
            return v___x_1651_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ =
        l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0;
    v___x_1658_ = lean_string_length(v___x_1657_);
    return v___x_1658_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3_once), _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3);
    v___x_1660_ = lean_nat_to_int(v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0(
    mut v_xs_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    v___x_1669_ = lean_array_get_size(v_xs_1668_);
    v___x_1670_ = leanh::lean_unsigned_to_nat(0);
    v___x_1671_ = lean_nat_dec_eq(v___x_1669_, v___x_1670_);
    if v___x_1671_ == 0 {
        let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1672_ = lean_array_to_list(v_xs_1668_);
        v___x_1673_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1;
        v___x_1674_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0(v___x_1672_, v___x_1673_);
        v___x_1675_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4_once), _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4);
        v___x_1676_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5;
        v___x_1677_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
        leanh::lean_ctor_set(v___x_1677_, 1, v___x_1674_);
        v___x_1678_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6;
        v___x_1679_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1679_, 0, v___x_1677_);
        leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
        v___x_1680_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1680_, 0, v___x_1675_);
        leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
        v___x_1681_ = l_Std_Format_fill(v___x_1680_);
        return v___x_1681_;
    } else {
        let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1668_);
        v___x_1682_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8;
        return v___x_1682_;
    }
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = leanh::lean_unsigned_to_nat(13);
    v___x_1693_ = lean_nat_to_int(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg(
    mut v_x_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_groupname_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gid_1699_: u64 = 0;
    let mut v_members_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_groupname_1698_ = leanh::lean_ctor_get(v_x_1697_, 0);
    leanh::lean_inc_ref(v_groupname_1698_);
    v_gid_1699_ = leanh::lean_ctor_get_uint64(
        v_x_1697_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_members_1700_ = leanh::lean_ctor_get(v_x_1697_, 1);
    leanh::lean_inc_ref(v_members_1700_);
    leanh::lean_dec_ref(v_x_1697_);
    v___x_1701_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1702_ = l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3;
    v___x_1703_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4_once
        ),
        _init_l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4,
    );
    v___x_1704_ = l_String_quote(v_groupname_1698_);
    v___x_1705_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1705_, 0, v___x_1704_);
    v___x_1706_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1706_, 0, v___x_1703_);
    leanh::lean_ctor_set(v___x_1706_, 1, v___x_1705_);
    v___x_1707_ = 0;
    v___x_1708_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1708_, 0, v___x_1706_);
    leanh::lean_ctor_set_uint8(
        v___x_1708_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    v___x_1709_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1709_, 0, v___x_1702_);
    leanh::lean_ctor_set(v___x_1709_, 1, v___x_1708_);
    v___x_1710_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1711_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1711_, 0, v___x_1709_);
    leanh::lean_ctor_set(v___x_1711_, 1, v___x_1710_);
    v___x_1712_ = leanh::lean_box(1);
    v___x_1713_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1713_, 0, v___x_1711_);
    leanh::lean_ctor_set(v___x_1713_, 1, v___x_1712_);
    v___x_1714_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7;
    v___x_1715_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1715_, 0, v___x_1713_);
    leanh::lean_ctor_set(v___x_1715_, 1, v___x_1714_);
    v___x_1716_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    leanh::lean_ctor_set(v___x_1716_, 1, v___x_1701_);
    v___x_1717_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9,
    );
    v___x_1718_ = lean_uint64_to_nat(v_gid_1699_);
    v___x_1719_ = l_Nat_reprFast(v___x_1718_);
    v___x_1720_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1720_, 0, v___x_1719_);
    v___x_1721_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1721_, 0, v___x_1717_);
    leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
    v___x_1722_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1722_, 0, v___x_1721_);
    leanh::lean_ctor_set_uint8(
        v___x_1722_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    v___x_1723_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1723_, 0, v___x_1716_);
    leanh::lean_ctor_set(v___x_1723_, 1, v___x_1722_);
    v___x_1724_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1724_, 0, v___x_1723_);
    leanh::lean_ctor_set(v___x_1724_, 1, v___x_1710_);
    v___x_1725_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
    leanh::lean_ctor_set(v___x_1725_, 1, v___x_1712_);
    v___x_1726_ = l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6;
    v___x_1727_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1727_, 0, v___x_1725_);
    leanh::lean_ctor_set(v___x_1727_, 1, v___x_1726_);
    v___x_1728_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    leanh::lean_ctor_set(v___x_1728_, 1, v___x_1701_);
    v___x_1729_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1730_ = l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0(
        v_members_1700_,
    );
    v___x_1731_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1731_, 0, v___x_1729_);
    leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
    v___x_1732_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1732_, 0, v___x_1731_);
    leanh::lean_ctor_set_uint8(
        v___x_1732_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    v___x_1733_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1733_, 0, v___x_1728_);
    leanh::lean_ctor_set(v___x_1733_, 1, v___x_1732_);
    v___x_1734_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1735_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1736_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1736_, 0, v___x_1735_);
    leanh::lean_ctor_set(v___x_1736_, 1, v___x_1733_);
    v___x_1737_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1738_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1738_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1738_, 1, v___x_1737_);
    v___x_1739_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1739_, 0, v___x_1734_);
    leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
    v___x_1740_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    leanh::lean_ctor_set_uint8(
        v___x_1740_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprGroupInfo_repr(
    mut v_x_1741_: *mut leanh::LeanObject,
    mut v_prec_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg(v_x_1741_);
    return v___x_1743_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprGroupInfo_repr___boxed(
    mut v_x_1744_: *mut leanh::LeanObject,
    mut v_prec_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Std_Internal_UV_System_instReprGroupInfo_repr(v_x_1744_, v_prec_1745_);
    leanh::lean_dec(v_prec_1745_);
    return v_res_1746_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u64 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0;
    v___x_1752_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1753_ = l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0;
    v___x_1754_ = leanh::lean_alloc_ctor(0, 2, (8) as u32);
    leanh::lean_ctor_set(v___x_1754_, 0, v___x_1753_);
    leanh::lean_ctor_set(v___x_1754_, 1, v___x_1751_);
    leanh::lean_ctor_set_uint64(
        v___x_1754_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1752_,
    );
    return v___x_1754_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1,
    );
    return v___x_1755_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedGroupInfo()
-> *mut leanh::LeanObject {
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Std_Internal_UV_System_instInhabitedGroupInfo_default;
    return v___x_1756_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg(
    mut v_x_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sysname_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_release_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_machine_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sysname_1776_ = leanh::lean_ctor_get(v_x_1775_, 0);
    leanh::lean_inc_ref(v_sysname_1776_);
    v_release_1777_ = leanh::lean_ctor_get(v_x_1775_, 1);
    leanh::lean_inc_ref(v_release_1777_);
    v_version_1778_ = leanh::lean_ctor_get(v_x_1775_, 2);
    leanh::lean_inc_ref(v_version_1778_);
    v_machine_1779_ = leanh::lean_ctor_get(v_x_1775_, 3);
    leanh::lean_inc_ref(v_machine_1779_);
    leanh::lean_dec_ref(v_x_1775_);
    v___x_1780_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1781_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3;
    v___x_1782_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1783_ = l_String_quote(v_sysname_1776_);
    v___x_1784_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1783_);
    v___x_1785_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1785_, 0, v___x_1782_);
    leanh::lean_ctor_set(v___x_1785_, 1, v___x_1784_);
    v___x_1786_ = 0;
    v___x_1787_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1787_, 0, v___x_1785_);
    leanh::lean_ctor_set_uint8(
        v___x_1787_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1788_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1788_, 0, v___x_1781_);
    leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
    v___x_1789_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1790_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1790_, 0, v___x_1788_);
    leanh::lean_ctor_set(v___x_1790_, 1, v___x_1789_);
    v___x_1791_ = leanh::lean_box(1);
    v___x_1792_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1792_, 0, v___x_1790_);
    leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
    v___x_1793_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5;
    v___x_1794_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1794_, 0, v___x_1792_);
    leanh::lean_ctor_set(v___x_1794_, 1, v___x_1793_);
    v___x_1795_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1795_, 0, v___x_1794_);
    leanh::lean_ctor_set(v___x_1795_, 1, v___x_1780_);
    v___x_1796_ = l_String_quote(v_release_1777_);
    v___x_1797_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    v___x_1798_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1798_, 0, v___x_1782_);
    leanh::lean_ctor_set(v___x_1798_, 1, v___x_1797_);
    v___x_1799_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1799_, 0, v___x_1798_);
    leanh::lean_ctor_set_uint8(
        v___x_1799_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1800_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1800_, 0, v___x_1795_);
    leanh::lean_ctor_set(v___x_1800_, 1, v___x_1799_);
    v___x_1801_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 1, v___x_1789_);
    v___x_1802_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1802_, 0, v___x_1801_);
    leanh::lean_ctor_set(v___x_1802_, 1, v___x_1791_);
    v___x_1803_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7;
    v___x_1804_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1804_, 0, v___x_1802_);
    leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    v___x_1805_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    leanh::lean_ctor_set(v___x_1805_, 1, v___x_1780_);
    v___x_1806_ = l_String_quote(v_version_1778_);
    v___x_1807_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1807_, 0, v___x_1806_);
    v___x_1808_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1808_, 0, v___x_1782_);
    leanh::lean_ctor_set(v___x_1808_, 1, v___x_1807_);
    v___x_1809_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
    leanh::lean_ctor_set_uint8(
        v___x_1809_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1810_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1810_, 0, v___x_1805_);
    leanh::lean_ctor_set(v___x_1810_, 1, v___x_1809_);
    v___x_1811_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    leanh::lean_ctor_set(v___x_1811_, 1, v___x_1789_);
    v___x_1812_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    leanh::lean_ctor_set(v___x_1812_, 1, v___x_1791_);
    v___x_1813_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9;
    v___x_1814_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1814_, 0, v___x_1812_);
    leanh::lean_ctor_set(v___x_1814_, 1, v___x_1813_);
    v___x_1815_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    leanh::lean_ctor_set(v___x_1815_, 1, v___x_1780_);
    v___x_1816_ = l_String_quote(v_machine_1779_);
    v___x_1817_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    v___x_1818_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1818_, 0, v___x_1782_);
    leanh::lean_ctor_set(v___x_1818_, 1, v___x_1817_);
    v___x_1819_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
    leanh::lean_ctor_set_uint8(
        v___x_1819_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1820_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1815_);
    leanh::lean_ctor_set(v___x_1820_, 1, v___x_1819_);
    v___x_1821_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1822_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1823_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1823_, 0, v___x_1822_);
    leanh::lean_ctor_set(v___x_1823_, 1, v___x_1820_);
    v___x_1824_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1825_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1825_, 0, v___x_1823_);
    leanh::lean_ctor_set(v___x_1825_, 1, v___x_1824_);
    v___x_1826_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1826_, 0, v___x_1821_);
    leanh::lean_ctor_set(v___x_1826_, 1, v___x_1825_);
    v___x_1827_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1827_, 0, v___x_1826_);
    leanh::lean_ctor_set_uint8(
        v___x_1827_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    return v___x_1827_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprUnameInfo_repr(
    mut v_x_1828_: *mut leanh::LeanObject,
    mut v_prec_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg(v_x_1828_);
    return v___x_1830_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprUnameInfo_repr___boxed(
    mut v_x_1831_: *mut leanh::LeanObject,
    mut v_prec_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Std_Internal_UV_System_instReprUnameInfo_repr(v_x_1831_, v_prec_1832_);
    leanh::lean_dec(v_prec_1832_);
    return v_res_1833_;
}
pub unsafe fn l_Std_Internal_UV_System_getProcessTitle___boxed(
    mut v_a_00___x40___internal___hyg_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = lean_uv_get_process_title();
    return v_res_1842_;
}
pub unsafe fn l_Std_Internal_UV_System_setProcessTitle___boxed(
    mut v_a_00___x40___internal___hyg_1845_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = lean_uv_set_process_title(v_a_00___x40___internal___hyg_1845_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1845_);
    return v_res_1847_;
}
pub unsafe fn l_Std_Internal_UV_System_uptime___boxed(
    mut v_a_00___x40___internal___hyg_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1850_ = lean_uv_uptime();
    return v_res_1850_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPid___boxed(
    mut v_a_00___x40___internal___hyg_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1853_ = lean_uv_os_getpid();
    return v_res_1853_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPpid___boxed(
    mut v_a_00___x40___internal___hyg_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = lean_uv_os_getppid();
    return v_res_1856_;
}
pub unsafe fn l_Std_Internal_UV_System_cpuInfo___boxed(
    mut v_a_00___x40___internal___hyg_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1859_ = lean_uv_cpu_info();
    return v_res_1859_;
}
pub unsafe fn l_Std_Internal_UV_System_cwd___boxed(
    mut v_a_00___x40___internal___hyg_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = lean_uv_cwd();
    return v_res_1862_;
}
pub unsafe fn l_Std_Internal_UV_System_chdir___boxed(
    mut v_a_00___x40___internal___hyg_1865_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = lean_uv_chdir(v_a_00___x40___internal___hyg_1865_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1865_);
    return v_res_1867_;
}
pub unsafe fn l_Std_Internal_UV_System_osHomedir___boxed(
    mut v_a_00___x40___internal___hyg_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = lean_uv_os_homedir();
    return v_res_1870_;
}
pub unsafe fn l_Std_Internal_UV_System_osTmpdir___boxed(
    mut v_a_00___x40___internal___hyg_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = lean_uv_os_tmpdir();
    return v_res_1873_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPasswd___boxed(
    mut v_a_00___x40___internal___hyg_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = lean_uv_os_get_passwd();
    return v_res_1876_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetGroup___boxed(
    mut v_a_00___x40___internal___hyg_1879_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1881_: u64 = 0;
    let mut v_res_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1881_ =
        leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_1879_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1879_);
    v_res_1882_ = lean_uv_os_get_group(v_a_00___x40___internal___hyg_1__boxed_1881_);
    return v_res_1882_;
}
pub unsafe fn l_Std_Internal_UV_System_osEnviron___boxed(
    mut v_a_00___x40___internal___hyg_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1885_ = lean_uv_os_environ();
    return v_res_1885_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetenv___boxed(
    mut v_a_00___x40___internal___hyg_1888_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1890_ = lean_uv_os_getenv(v_a_00___x40___internal___hyg_1888_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1888_);
    return v_res_1890_;
}
pub unsafe fn l_Std_Internal_UV_System_osSetenv___boxed(
    mut v_a_00___x40___internal___hyg_1894_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1895_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = lean_uv_os_setenv(
        v_a_00___x40___internal___hyg_1894_,
        v_a_00___x40___internal___hyg_1895_,
    );
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1895_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1894_);
    return v_res_1897_;
}
pub unsafe fn l_Std_Internal_UV_System_osUnsetenv___boxed(
    mut v_a_00___x40___internal___hyg_1900_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = lean_uv_os_unsetenv(v_a_00___x40___internal___hyg_1900_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1900_);
    return v_res_1902_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetHostname___boxed(
    mut v_a_00___x40___internal___hyg_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = lean_uv_os_gethostname();
    return v_res_1905_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPriority___boxed(
    mut v_a_00___x40___internal___hyg_1908_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1910_: u64 = 0;
    let mut v_res_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1910_ =
        leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_1908_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1908_);
    v_res_1911_ = lean_uv_os_getpriority(v_a_00___x40___internal___hyg_1__boxed_1910_);
    return v_res_1911_;
}
pub unsafe fn l_Std_Internal_UV_System_osSetPriority___boxed(
    mut v_a_00___x40___internal___hyg_1915_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1916_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1918_: u64 = 0;
    let mut v_a_00___x40___internal___hyg_2__boxed_1919_: u64 = 0;
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1918_ =
        leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_1915_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1915_);
    v_a_00___x40___internal___hyg_2__boxed_1919_ =
        leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_1916_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1916_);
    v_res_1920_ = lean_uv_os_setpriority(
        v_a_00___x40___internal___hyg_1__boxed_1918_,
        v_a_00___x40___internal___hyg_2__boxed_1919_,
    );
    return v_res_1920_;
}
pub unsafe fn l_Std_Internal_UV_System_osUname___boxed(
    mut v_a_00___x40___internal___hyg_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = lean_uv_os_uname();
    return v_res_1923_;
}
pub unsafe fn l_Std_Internal_UV_System_hrtime___boxed(
    mut v_a_00___x40___internal___hyg_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = lean_uv_hrtime();
    return v_res_1926_;
}
pub unsafe fn l_Std_Internal_UV_System_random___boxed(
    mut v_a_00___x40___internal___hyg_1929_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1931_: u64 = 0;
    let mut v_res_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1931_ =
        leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_1929_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1929_);
    v_res_1932_ = lean_uv_random(v_a_00___x40___internal___hyg_1__boxed_1931_);
    return v_res_1932_;
}
pub unsafe fn l_Std_Internal_UV_System_getrusage___boxed(
    mut v_a_00___x40___internal___hyg_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1935_ = lean_uv_getrusage();
    return v_res_1935_;
}
pub unsafe fn l_Std_Internal_UV_System_exePath___boxed(
    mut v_a_00___x40___internal___hyg_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = lean_uv_exepath();
    return v_res_1938_;
}
pub unsafe fn l_Std_Internal_UV_System_freeMemory___boxed(
    mut v_a_00___x40___internal___hyg_1940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1941_ = lean_uv_get_free_memory();
    return v_res_1941_;
}
pub unsafe fn l_Std_Internal_UV_System_totalMemory___boxed(
    mut v_a_00___x40___internal___hyg_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = lean_uv_get_total_memory();
    return v_res_1944_;
}
pub unsafe fn l_Std_Internal_UV_System_constrainedMemory___boxed(
    mut v_a_00___x40___internal___hyg_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = lean_uv_get_constrained_memory();
    return v_res_1947_;
}
pub unsafe fn l_Std_Internal_UV_System_availableMemory___boxed(
    mut v_a_00___x40___internal___hyg_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = lean_uv_get_available_memory();
    return v_res_1950_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_System(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Net(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Internal_UV_System_instInhabitedRUsage_default =
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedRUsage_default);
    l_Std_Internal_UV_System_instInhabitedRUsage =
        _init_l_Std_Internal_UV_System_instInhabitedRUsage();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedRUsage);
    l_Std_Internal_UV_System_instInhabitedCPUTimes_default =
        _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUTimes_default);
    l_Std_Internal_UV_System_instInhabitedCPUTimes =
        _init_l_Std_Internal_UV_System_instInhabitedCPUTimes();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUTimes);
    l_Std_Internal_UV_System_instInhabitedCPUInfo_default =
        _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUInfo_default);
    l_Std_Internal_UV_System_instInhabitedCPUInfo =
        _init_l_Std_Internal_UV_System_instInhabitedCPUInfo();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUInfo);
    l_Std_Internal_UV_System_instInhabitedGroupInfo_default =
        _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedGroupInfo_default);
    l_Std_Internal_UV_System_instInhabitedGroupInfo =
        _init_l_Std_Internal_UV_System_instInhabitedGroupInfo();
    leanh::lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedGroupInfo);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_System(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_System(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Net(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_System(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_System(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_System(builtin);
}